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

module TMap = Term.TermMap
module IMap = Map.Make(struct type t = int let compare = compare end)
module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))

let solver_ref = ref None

module BddSolver : sig

  (* BddSolver context. *)
  type t

  (* Creates a BddSolver context. *)
  val mk_bdd_solver : TransSys.t -> t

  (* Queries the base instance, returns [None] if it is unsat, otherwise
     [Some] of a model. *)
  val query_base : t -> Term.t -> ((Var.t * Term.t) list) option

  (* Asserts some terms in the previous state under an activation
     literal. Calling this again deactivates the previous terms. *)
  val assert_at_minus_one : t -> Term.t -> unit

  (* Checks if some terms can be falsified in the next step, assuming
     whatever is asserted at minus one. *)
  val query_step :
    t -> Term.t -> ((Var.t * Term.t) list) option

  (* Deletes the underlying solver. *)
  val delete : t -> unit

end = struct

  type t = {

    (* The solver of the context. *)
    solver : Solver.t ;

    (* The system associated with this context. *)
    sys : TransSys.t ;

    (* The last activation literal used, as a term. Upon creation,
       activates init. The actlit is already declared in the
       solver. *)
    mutable actlit : Term.t ;

  }

  (* Creates a BddSolver context. *)
  let mk_bdd_solver sys =

    (* Creating solver. *)
    let solver =
      TransSys.get_logic sys
      |> Solver.new_solver ~produce_assignments: true
    in

    (* Declaring state variables. *)
    TransSys.iter_state_var_declarations
      sys (Solver.declare_fun solver) ;

    (* Init actlit, as a term. *)
    let init_actlit =
      (* Getting a fresh actlit for init. *)
      let actlit = Actlit.fresh_actlit () in
      (* Declaring it. *)
      Solver.declare_fun solver actlit ;
      (* Term version. *)
      Actlit.term_of_actlit actlit
    in
    
    (* Defining things. *)
    TransSys.iter_uf_definitions
      sys (Solver.define_fun solver) ;

    (* Asserting actlit implication for init. *)
    Term.mk_implies [
      init_actlit ; TransSys.init_of_bound sys Numeral.zero
    ] |> Solver.assert_term solver ;

    (* Asserting invariants at 0 and 1. *)
    TransSys.invars_of_bound sys Numeral.zero
    |> Solver.assert_term solver ;
    TransSys.invars_of_bound sys Numeral.one
    |> Solver.assert_term solver ;

    (* Building context. *)
    { solver ; sys ; actlit = init_actlit }

  (* Queries the base instance, returns [None] if it is unsat, otherwise
     [Some] of a model. *)
  let query_base { solver ; sys ; actlit } term =

    (* Actlit for [term]. *)
    let term_actlit =
      let actlit_uf = Actlit.fresh_actlit () in
      Solver.declare_fun solver actlit_uf ;
      Actlit.term_of_actlit actlit_uf
    in

    (* Asserting implication between actlit and term. *)
    Term.mk_implies [
      term_actlit ; Term.mk_not term
    ] |> Solver.assert_term solver ;

    (* Function to run if sat. *)
    let if_sat () =
      Some (
        (* Variables we want to know the value of. *)
        TransSys.vars_of_bounds sys Numeral.zero Numeral.zero
        (* Actually getting the values. *)
        |> Solver.get_model solver
      )
    in

    (* Function to run if unsat. *)
    let if_unsat () = None in

    (* New invariants. *)
    let new_invs, _ =
      (* Receiving messages. *)
      Event.recv ()
      (* Updating transition system. *)
      |> Event.update_trans_sys sys
      (* Extracting invariant module/term pairs. *)
    in

    (* Asserting new invariants at 0 and 1. *)
    ( match new_invs with
      | [] -> ()
      | _ ->
        new_invs
        |> List.iter
            (fun (_, inv) ->
              Term.bump_state Numeral.zero inv
              |> Solver.assert_term solver ;
              Term.bump_state Numeral.one inv
              |> Solver.assert_term solver) ) ;

    (* Check-sat-ing. *)
    let result =
      Solver.check_sat_assuming
        solver if_sat if_unsat [ actlit ; term_actlit ]
    in

    (* Deactivating actlit. *)
    Term.mk_not term_actlit
    |> Solver.assert_term solver ;

    (* Returning result. *)
    result

  (* Asserts some terms in the previous state under an activation
     literal. Calling this again deactivates the previous terms. *)
  let assert_at_minus_one ({ solver ; actlit } as context) term =

    (* Deactivating previous actlit. *)
    Term.mk_not actlit |> Solver.assert_term solver ;

    (* Actlit for [term]. *)
    let term_actlit =
      let actlit_uf = Actlit.fresh_actlit () in
      Solver.declare_fun solver actlit_uf ;
      Actlit.term_of_actlit actlit_uf
    in

    (* Asserting implication between actlit and term. *)
    Term.mk_implies [
      term_actlit ; term
    ] |> Solver.assert_term solver ;

    (* Updating actlit in context. *)
    context.actlit <- term_actlit


  (* Checks if some terms can be falsified in the next step, assuming
     whatever is asserted at minus one. *)
  let query_step { solver ; sys ; actlit } term =

    (* Actlit for [term]. *)
    let term_actlit =
      let actlit_uf = Actlit.fresh_actlit () in
      Solver.declare_fun solver actlit_uf ;
      Actlit.term_of_actlit actlit_uf
    in

    (* Asserting implication between actlit and term bumped @1. *)
    Term.mk_implies [
      term_actlit ; Term.bump_state Numeral.one term |> Term.mk_not
    ] |> Solver.assert_term solver ;

    (* Function to run if sat. *)
    let if_sat () =
      Some (
        (* Variables we want to know the value of. *)
        TransSys.vars_of_bounds sys Numeral.one Numeral.one
        (* Actually getting the values. *)
        |> Solver.get_model solver
        (* Bumping back to zero. *)
        |> List.map
          ( fun (v,t) ->
            (Var.bump_offset_of_state_var_instance Numeral.(~- one) v,
             t) )
      )
    in

    (* Function to run if unsat. *)
    let if_unsat () = None in

    (* New invariants. *)
    let new_invs, _ =
      (* Receiving messages. *)
      Event.recv ()
      (* Updating transition system. *)
      |> Event.update_trans_sys sys
      (* Extracting invariant module/term pairs. *)
    in

    (* Asserting new invariants at 0 and 1. *)
    ( match new_invs with
      | [] -> ()
      | _ ->
        new_invs
        |> List.iter
            (fun (_, inv) ->
              Term.bump_state Numeral.zero inv
              |> Solver.assert_term solver ;
              Term.bump_state Numeral.one inv
              |> Solver.assert_term solver) ) ;

    (* Check-sat-ing. *)
    let result =
      Solver.check_sat_assuming
        solver if_sat if_unsat [ actlit ; term_actlit ]
    in

    (* Deactivating actlit. *)
    Term.mk_not term_actlit
    |> Solver.assert_term solver ;

    (* Returning result. *)
    result


  (* Deletes the underlying solver. *)
  let delete { solver } = Solver.delete_solver solver

end

module Abstractor : sig

  (* An abstractor context. *)
  type t

  (* Creates an abstractor context from a list of predicates. *)
  val mk_abstractor : Term.TermSet.t -> t

  (* Adds a cube to an abstractor base on an evaluation function. *)
  val abstractor_add_cube : t -> (Term.t -> bool) -> t

  (* The formula corresponding to this abstractor. *)
  val formula_of_abstractor : t -> Term.t

  (* Prints the bdd inside the abstractor as a dot file. *)
  val print_to : t -> string -> unit

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

  (* Prints the bdd insade the abstractor as a dot file. *)
  let print_to { bdd } file =
    Bdd.print_to_dot bdd file

  (* Creates an abstractor context from a list of predicates. *)
  let mk_abstractor predicates_set =

    (* Getting the list of predicates. *)
    let predicates = Term.TermSet.elements predicates_set in

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

    debug invGenBdd
      "Concrete map: @[<v>%a@]"
      (pp_print_list
         (fun ppf (term,index) ->
           Format.fprintf ppf "%3i <- %a"
             index Term.pp_print_term term)
         "@ ") (TMap.bindings concrete_map) in

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
open BddSolver

(* Iterates on the base case until the abstractor includes the initial
   states. *)
let rec base_case iteration sys solver abstractor =

  print_to abstractor (Format.sprintf "dot/bdd-base-%03i.dot" iteration) ;

  let _ = debug invGenBdd "Checking base case." in () in
  
  match
    formula_of_abstractor abstractor |> query_base solver
  with
      
    | None ->
      debug invGenBdd "Unsat." in
      (* Base is unsat, done. *)
      abstractor

    | Some model ->
      debug invGenBdd "Sat." in
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
        solver
        (* Building new abstractor. *)
        (abstractor_add_cube abstractor eval)


let rec step_case iteration sys solver abstractor =

  let _ = 
    print_to abstractor (Format.sprintf "dot/bdd-step-%03i-000.dot" iteration)
  in

  debug invGenBdd "Step case is at %i." iteration in

  debug invGenBdd "Activating current term." in

  let term = formula_of_abstractor abstractor in

  let _ = assert_at_minus_one solver term in

  debug invGenBdd "Checking if term is invariant." in

  match query_step solver term with

    | None -> (
      debug invGenBdd "It is an invariant \\(^o^)/." in
      Event.invariant term )

    | Some model -> (
      debug invGenBdd "Not an invariant, entering loop." in
      loop iteration 1 sys solver abstractor model )

and loop iteration inner_iteration sys solver abstractor model =

    let _ = 
      print_to abstractor
        (Format.sprintf "dot/bdd-step-%03i-%03i.dot" iteration inner_iteration)
    in

    debug invGenBdd
      "Starting loop %i:%i."
      iteration
      inner_iteration in

    (* Building eval function. *)
    let eval term =
      Eval.eval_term
        (TransSys.uf_defs sys)
        model
        term
      |> Eval.bool_of_value
    in

    (* Updating abstractor. *)
    let abstractor' = abstractor_add_cube abstractor eval in

    (* Getting new term. *)
    let term = formula_of_abstractor abstractor' in

    debug invGenBdd
      "Querying step." in

    (* Querying step. *)
    match query_step solver term with
      | None ->
        (*debug invGenBdd "Unsat, going back to step_case." in*)
        step_case (iteration + 1) sys solver abstractor'

      | Some model ->
        (*debug invGenBdd "Sat, looping." in*)
        loop
          iteration
          (inner_iteration + 1)
          sys
          solver
          abstractor'
          model


let solver_ref = ref None      

let main trans =

  let solver = mk_bdd_solver trans in
  solver_ref := Some solver ;

  let _ = debug invGenBdd "Starting bdd inv gen." in () in

  let rec get_last = function
    | [ (sys,terms) ] -> terms
    | _ :: tail -> get_last tail
    | [] -> raise (Invalid_argument "get_last: empty list.")
  in

  (* Generating candidate terms. *)
  let candidate_terms =
    InvGenCandTermGen.generate_candidate_terms false trans
    |> fst |> get_last
    |> Term.TermSet.filter (fun t -> not ( t == Term.t_true || t == Term.t_false))
  in

  (* Launching base case. *)
  base_case 1 trans solver (mk_abstractor candidate_terms)
  |> step_case 1 trans solver

(* Cleans up things on exit. *)
let on_exit _ =
  
  (* Destroying solver if one was created. *)
  ( match !solver_ref with
    | None -> ()
    | Some solver -> delete solver )

                      
(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

