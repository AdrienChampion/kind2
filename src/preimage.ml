(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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
open Actlit

(* Exception thrown when incrementing a context with an empty [nxt]. *)
exception NoPreimage of int

(*  Internaly the context maintains a solver with the transition relation
    at [(0,1)]. Three actlits are used, and changed by [inc].

    * [src_actlit]:
      activates the terms we are computing the preimage of, at [1].
    * [blk_actlit]:
      activates the negation of the disjuncts of the preimage we have computed
      this far, _for this iteration_, at [0].

    Function [inc] increments the context so that [get_disjunct] computes the
    preimage of the one it was computing before the call to [inc].
*)

(* Stores info needed to compute preimages. *)
type context = {
  solver: SMTSolver.t ;
  sys: TransSys.t ;
  mutable src: Term.t ;
  mutable nxt: Term.t list ;
  mutable src_act: Term.t ;
  mutable blk_act: Term.t ;
  mutable count: int ;
  blocking: bool ;
}

(* The system stored in a context. *)
let get_sys { sys } = sys

(* The number of times a system has been incremented. *)
let get_k { count } = count

(* Generates a fresh actlit, declares it, and returns the corresponding
   term. *)
let get_actlit solver =
  let fresh = fresh_actlit () in
  SMTSolver.declare_fun solver fresh ;
  term_of_actlit fresh

(* Asserts an implication between an actlit and a term. *)
let activate solver actlit term =
  Term.mk_implies [ actlit ; term ]
  |> SMTSolver.assert_term solver

(* Creates a new context from a transition system and a term to compute the
   preimages of. *)
let mk_context ?(blocking=true) sys src =

  (* Making sure [src] only mentions variables at [0]. *)
  ( match Term.var_offsets_of_term src with
    (* Weird but why not. *)
    | None, None -> ()
    (* Legal. *)
    | Some lo, Some hi
      when Numeral.(equal lo zero) && Numeral.(equal hi zero) -> ()
    (* Illegal. *)
    | Some(lo), Some(hi) ->
      Format.asprintf
        "unexpected offset for source in preimage computation: [%a,%a]"
        Numeral.pp_print_numeral lo Numeral.pp_print_numeral hi
      |> failwith
      | _ -> failwith "unexpected result for [Term.var_offsets_of_term]") ;

  (* Creating solver. *)
  let solver =
    SMTSolver.create_instance
      ~produce_assignments:true (TransSys.get_logic sys) (Flags.smtsolver ())
  in

  (* Defining uf's and declaring variables. *)
  TransSys.init_define_fun_declare_vars_of_bounds
    sys
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    Numeral.(~- one) Numeral.one ;

  (* Asserting transition relation [(0,1)]. *)
  TransSys.trans_of_bound sys Numeral.one
  |> SMTSolver.assert_term solver ;

  (* Asserting invariants at [0] and [1]. *)
  [ TransSys.invars_of_bound sys Numeral.zero ;
    TransSys.invars_of_bound sys Numeral.one ]
  |> List.iter (SMTSolver.assert_term solver) ;

  SMTSolver.trace_comment solver "Initialization for preimage computation." ;

  (* Getting fresh actlits, declaring them in the process. *)
  let src_act, blk_act = get_actlit solver, get_actlit solver in

  (* Asserting implication with [src@1]. *)
  Term.bump_state Numeral.one src |> activate solver src_act ;

  (* Originally zero incrementations. *)
  let count = 0 in

  (* Ready to roll, returning context. *)
  { solver ; sys ; src ; nxt = [] ; src_act ; blk_act ; count ; blocking }

(* Destroys a context, i.e. destroys the internal solver instance. *)
let destroy { solver } =
  SMTSolver.delete_instance solver

(* Computes a new disjunct of the current preimage. *)
let inc ({ solver ; nxt ; blk_act ; count ; blocking } as ctxt) =

  count + 1
  |> Format.sprintf "Incrementing preimage computation to %d"
  |> SMTSolver.trace_comment solver ;

  (* Cannot increment if instance is not unsat. *)
  SMTSolver.trace_comment solver "Sanity check: instance should be unsat." ;
  SMTSolver.check_sat_assuming
    solver
    (fun () -> failwith "increment called on sat instance")
    (fun () -> ())
    [ ctxt.src_act ; blk_act ] ;

  (* If next is empty then there is no preimage. *)
  let nxt = match nxt with
    | [] -> NoPreimage count |> raise
    | l  -> Term.mk_or l
  in

  (* New [src] is the conjunction of the terms in [nxt]. *)
  ctxt.src <- nxt ;
  (* New [nxt] is empty. *)
  ctxt.nxt <- [] ;
  (* New [src_act] is the old [nxt_act]. *)
  ctxt.src_act <- get_actlit solver ;
  (* Keeping [blk_act] if [blocking], getting a fresh one otherwise. *)
  ctxt.blk_act <- if blocking then blk_act else get_actlit solver ;
  (* Incrementing count. *)
  ctxt.count <- count + 1 ;

  (* Asserting implication for the new [src]. *)
  Term.bump_state Numeral.one nxt |> activate solver ctxt.src_act ;

  ()

(* Computes a new disjunct of the preimage. *)
let get_disjunct (
  { sys ; solver ; src ; nxt ; src_act ; blk_act } as ctxt
) =

  match
    (* Looking for a predecessor of [src@1] outside of [blk@0]. *)
    SMTSolver.check_sat_assuming
      solver
      (fun () -> Some (SMTSolver.get_model solver))
      (fun () -> None)
      [ src_act ; blk_act ]
  with

  (* Unsat. *)
  | None -> None

  (* Sat, generalizing model. *)
  | Some model ->
    (* Term to extrapolate. *)
    let term =
      (TransSys.trans_of_bound sys Numeral.one) ::
      (Term.bump_state Numeral.one src) :: []
      |> Term.mk_and
    in
    (* Getting primed variables in the transition system. *)
    let vars = 
      Var.VarSet.elements
        (Term.vars_at_offset_of_term (Numeral.one) term) 
    in
    (* Generalizing. *)
    let cube = QE.generalize sys (TransSys.uf_defs sys) model vars term in
    let term' = Term.mk_and cube in

    (* Memorizing term for next iteration. *)
    ctxt.nxt <- term' :: ctxt.nxt ;
    (* Blocking this term at [0]. *)
    Term.mk_not term' |> activate solver blk_act ;

    (* Done. *)
    Some cube

(* Test function. *)
let test sys =
  let space () = Format.printf "@." in

  Format.printf "|===| Starting preimage computation.@.@." ;

  let props = TransSys.props_of_bound sys Numeral.zero in
  TransSys.props_list_of_bound sys Numeral.zero
  |> Format.printf
      "  props: @[<hv>%a@]@."
      ( pp_print_list (fun ppf (n,t) ->
          Format.fprintf ppf "| %10s = %a" n Term.pp_print_term t)
          "@," ) ;
  Format.printf "  term:  | @[<hv>%a@]@." Term.pp_print_term props ;
  space () ;

  Format.printf "Creating context..." ;
  let context = Term.mk_not props |> mk_context sys in
  Format.printf " done.@.@." ;
  space () ;

  let rec loop count =
    Format.printf "| getting disjunct %d:@." count ;
    match get_disjunct context with
    | None -> Format.printf "| > unsat@.@."
    | Some cube ->
      Format.printf
        "| > cube: @[<v>%a@]@.|@."
        (pp_print_list Term.pp_print_term "@,") cube ;
      count + 1 |> loop
  in

  let rec big_loop () =
    get_k context |> Format.printf "At iteration %d@." ;
    loop 0 ;
    Format.printf "Press [Enter] to keep going. @?" ;
    read_line () |> ignore ;
    space () ;
    Format.printf "Incrementing context.@." ;
    let iter = try inc context ; true with NoPreimage k ->
      Format.printf "No more preimages, done at %d.@." k ; false
    in
    if iter then big_loop ()
  in

  big_loop () ;

  space () ;

  ()


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
