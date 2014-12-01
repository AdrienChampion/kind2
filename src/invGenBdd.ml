(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

 *)

open Lib

module LSD = LockStepDriver
module TMap = Term.TermMap
module IMap = Map.Make(struct type t = int let compare = compare end)

let solver_ref = ref None

module Abstractor : sig

  (* An abstractor context. *)
  type t

  (* Creates an abstractor context from a list of predicates. *)
  val mk_abstractor : Term.t list -> t

  (* Adds a cube to an abstractor base on an evaluation function. *)
  val abstractor_add_cube : t -> (Term.t -> bool) -> t

  (* The formula corresponding to this abstractor. *)
  val formula_of_abstractor : t -> Term.t

end = struct

  (* An abstractor context. *)
  type t = {

    (* Predicates of the concrete domain. *)
    concrete_domain: Term.t list ;

    (* Map from concrete elements (predicates) to abstract elements
       (integers). *)
    concrete_map : int TMap.t ;

    (* Map from abstract elements (integers) to concrete elements
       (predicates). *)
    abstract_map : Term.t IMap.t ;

    (* The bdd of the abstractor. *)
    bdd : Bdd.t ;

  }

  (* Creates an abstractor context from a list of predicates. *)
  let mk_abstractor predicates =

    (* Making sure all the predicates are pairwise distinct. *)
    assert (
      List.for_all
        ( fun pred -> not (List.memq pred predicates) )
        predicates
    ) ;

    (* Setting max var for bdd module. *)
    List.length predicates |> Bdd.set_max_var ;

    (* Building the concrete and abstract mappings. *)
    let concrete_map, abstract_map, _ =
      predicates
      (* Iterating over the predicates. *)
      |> List.fold_left

          ( fun (c_map, a_map, index) concrete ->
            (* Abstract representation of pred. *)
            let abstract = index + 1 in
            (* Adding mappings. *)
            ( TMap.add concrete abstract c_map ),
            ( IMap.add abstract concrete a_map ),
            abstract )

          (* Starting with empty maps. *)
          (TMap.empty, IMap.empty, 0)
    in

    (* Building the abstractor context. *)
    { concrete_domain = predicates ;
      concrete_map ;
      abstract_map ;
      bdd = Bdd.zero }

  (* Converts a term to a bdd. *)
  let term_to_bdd { concrete_map } =

    (* The continuation is a list of triplets [(f, to_process,
       processed)] representing a destructed node. [processed] are the
       subterms already translated to bdds; [to_process] are the subterms
       not translated to bdds yet; [f] is the construction function to
       apply to the processed subterms to build the bdd corresponding to
       the original term. *)
    let rec continue continuation bdd =
      match continuation with
          
        | (f, to_process :: to_process_tail, processed) :: tail ->
          (* We still have subterms to process for this node, building
             continuation and going back to destruct things. *)
          bddfication
            ( (f, to_process_tail, bdd :: processed) :: tail )
            to_process
            
        | (f, [], processed) :: tail ->
          (* No more subterms to process. Applying constructive
             function and recursing. *)
          bdd :: processed
          (* Putting the processed subterms in the right order. *)
          |> List.rev
          (* Applying constructive function. *)
          |> f
          (* Recursing. *)
          |> continue tail

        | [] ->
          (* Continuation is empty, we're done. *)
          bdd

    (* Destructs nodes recursively to construct the bdd. *)
    and bddfication continuation term =
      
      (* Is the term a concrete element? *)
      try
        (* Attempting to construct a "leaf" bdd out of the term. *)
        (
          (* Catching true. *)
          if term == Term.t_true then Bdd.one
          (* Catching false. *)
          else if term == Term.t_false then Bdd.zero
          else
            TMap.find term concrete_map
            |> Bdd.mk_var
        )
        (* Continuing. *)
        |> continue continuation

      (* This term is not a leaf, destructing it. *)
      with
        | Not_found ->
          if Term.is_node term then

            let f =
              (* Destructing term to get construction function. *)
              match
                Term.node_symbol_of_term term
                |> Symbol.node_of_symbol
              with
                  
                | `AND ->
                  ( function
                    | h :: t ->
                      List.fold_left (fun bdd -> Bdd.mk_and bdd) h t
                    | _ ->
                      raise
                        (Invalid_argument
                           "bddfication (and).") )
                    
                | `OR ->
                  ( function
                    | h :: t ->
                      List.fold_left (fun bdd -> Bdd.mk_or bdd) h t
                    | _ ->
                      raise
                        (Invalid_argument
                           "bddfication (or).") )
                    
                | `NOT ->
                  ( function
                    | h :: [] -> Bdd.mk_not h
                    | _ ->
                      raise
                        (Invalid_argument
                           "bddfication (not).") )
                    
                | `IMPLIES ->
                  ( function
                    | [lhs ; rhs] -> Bdd.mk_imp lhs rhs
                    | _ ->
                      raise
                        (Invalid_argument
                           "bddfication (implies).") )
                    
                | _ ->
                  raise
                    (Invalid_argument
                       (Printf.sprintf
                          "[bddfication] unexpected application: %s"
                          (Term.string_of_term term)))
            in

            ( match Term.node_args_of_term term with
                
              | head :: tail ->
                (* Recursing. *)
                bddfication
                  (* New continuation with construction function and
                     kids to process. *)
                  ( (f, tail, []) :: continuation )
                  (* Bddfying first kid. *)
                  head

              | _ ->
                raise
                  (Invalid_argument
                     (Printf.sprintf
                        "[bddfication] application has no kids: %s"
                        (Term.string_of_term term))) )

          else
            raise
              (Invalid_argument
                 (Printf.sprintf
                    "[bddfication] not an application: %s"
                  (Term.string_of_term term)))
    in

    bddfication []

  (* Abstracts a predicate to its corresponding variable as a bdd. *)
  let alpha_predicate {concrete_map} eval predicate =
    try
      let var =
        TMap.find predicate concrete_map
        |> Bdd.mk_var
      in
      if eval predicate then var else Bdd.mk_not var
    with
      | Not_found ->
        raise
          (Invalid_argument
             (Printf.sprintf
                "[alpha_predicate] %s"
                (Term.string_of_term  predicate)))

  (* Abstraction function, converts a list of predicates --viewed as a
     conjunction-- to a bdd and adds it as a disjunction to the bdd in
     the abstractor. *)
  let alpha ({concrete_domain} as context) eval =
    match concrete_domain with
  
      | predicate :: tail ->

        List.fold_left
          (* Anding the predicates together... *)
          (fun and_bdd predicate ->
            alpha_predicate context eval predicate
              |> Bdd.mk_and and_bdd)
          (* ...starting from the first one... *)
          (alpha_predicate context eval predicate)
          (* ...and going through the rest. *)
          tail

      | [] -> Bdd.zero


  (* Concretizes a variable to its corresponding predicate. *)
  let gamma_variable {abstract_map} variable =
    try
      IMap.find variable abstract_map
    with
      | Not_found ->
          raise
          (Invalid_argument
             (Printf.sprintf
                "[gamma_variable] %i"
                variable))

  (* Concretization function, converts a bdd to a dnf of
     predicates. *)
  let gamma context =

    let rec continue dnf = function
      | (prefix, bdd) :: tail ->
        dnfication dnf tail prefix bdd
      | [] -> Term.mk_or dnf
    and dnfication dnf continuation prefix bdd =
      match Bdd.view bdd with
          
        | Bdd.Zero ->
          (* This branch is a dead one, continueing. *)
          continue dnf continuation
            
        | Bdd.One ->
          (* Building conjunction. *)
          let conjunction = Term.mk_and prefix in
          (* Valid branch, adding to dnf. *)
          continue (conjunction :: dnf) continuation
            
        | Bdd.Node (v,lo,hi) ->
          (* Concretizing variable. *)
          let concrete = gamma_variable context v in
          (* Recursing. *)
          dnfication
            dnf
            ( (Term.mk_not concrete :: prefix, lo)
              :: continuation )
            (concrete :: prefix)
            hi
    in

    dnfication [] [] [] context.bdd



  let abstractor_add_cube
      ({ concrete_domain ;
         concrete_map ;
         abstract_map ;
         bdd } as context)
      eval =

    (* Returning new abstractor. *)
    { concrete_domain ;
      concrete_map ;
      abstract_map ;
      (* Updating bdd. *)
      bdd = Bdd.mk_or bdd (alpha context eval)
    }

  let formula_of_abstractor = gamma

end

open Abstractor

(* Actlit for init, uf version. *)
let init_actlit_uf = Actlit.fresh_actlit ()
(* Actlit for init, term version. *)
let init_actlit = Actlit.term_of_actlit init_actlit_uf

(* Iterates on the base case until the abstractor includes the initial
   states. *)
let rec base_case iteration sys lsd abstractor =
  match
    LSD.query_base lsd sys [formula_of_abstractor abstractor]
  with
      
    | None ->
      (* Base is unsat, done. *)
      abstractor

    | Some model ->
      (* Building eval function. *)
      let eval term =
        Eval.eval_term
          (TransSys.uf_defs sys)
          model
          term
        |> Eval.bool_of_value
      in
      (* Looping. *)
      base_case
        (iteration + 1)
        sys
        lsd
        (* Building new abstractor. *)
        (abstractor_add_cube abstractor eval)


let lsd_ref = ref None      

let main trans =

  let lsd = LSD.create false trans in
  lsd_ref := Some lsd ;
  
  base_case 0 trans lsd (mk_abstractor []) |> ignore
  (* |> step_case 0 trans lsd *)

(* Cleans up things on exit. *)
let on_exit _ =
  
  (* Destroying lsd if one was created. *)
  ( match !lsd_ref with
    | None -> ()
    | Some lsd -> LSD.delete lsd )

                      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

