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

  (* Asserting implication with [not src@0]. *)
  Term.mk_not src |> activate solver blk_act ;

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

(* Given two atoms, checks if one implies the other. Returns an option of the
   least general one if the check succeeded, none otherwise.

   /!\ Assumes all variables in the atoms have the same offset. This is the
   case for the ones produced by QE. *)
let least_general_of atom1 atom2 =
  (* Get the state variables appearing in each atom. *)
  let svars1, svars2 =
    Term.state_vars_of_term atom1, Term.state_vars_of_term atom2
  in

  (* If the set of state vars is different, there is no least general atom. *)
  if not (StateVar.StateVarSet.equal svars1 svars2) then None else (

    (* State var count. *)
    let sv_count = StateVar.StateVarSet.cardinal svars1 in
    (* Destructing atoms. *)
    match Term.destruct atom1, Term.destruct atom2 with
    | Term.T.App (sym1, kids1), Term.T.App (sym2, kids2) ->
      if sym1 != sym2 then
        (* If one of the atoms is an equality, and there's only one variable
           mentioned then the equality is less general. *)
        match Symbol.node_of_symbol sym1, Symbol.node_of_symbol sym2 with
        | `EQ, _ when sv_count = 1 -> Some atom1
        | _, `EQ when sv_count = 1 -> Some atom2
        | _ -> None
      else (
        (* We should have no equality. *)
        assert ( Symbol.node_of_symbol sym1 <> `EQ ) ;

        (* Extracting lhs of applications. *)
        let lhs1, lhs2 = match kids1, kids2 with
          | [ lhs1 ; zero1 ], [ lhs2 ; zero2 ] -> (
            (* Making sure rhs is zero. *)
            if Term.is_numeral zero1 then (
              assert ( Term.numeral_of_term zero1 == Numeral.zero ) ;
              assert ( Term.numeral_of_term zero2 == Numeral.zero ) ;
            ) else (
              assert ( Term.decimal_of_term zero1 == Decimal.zero ) ;
              assert ( Term.decimal_of_term zero2 == Decimal.zero ) ;
            ) ;
            lhs1, lhs2
          )
          | _ ->
            Format.asprintf "unexpected atoms @[<h>%a@] and @[<h>%a@]@."
              Term.pp_print_term atom1 Term.pp_print_term atom2
            |> failwith
        in

        (* Both lhs should be applications. *)
        assert ( Term.is_node lhs1 ) ;
        assert ( Term.is_node lhs2 ) ;

        (* Both lhs should be a sum. *)
        assert (
          Term.node_symbol_of_term lhs1 |> Symbol.node_of_symbol = `PLUS
        ) ;
        assert (
          Term.node_symbol_of_term lhs2 |> Symbol.node_of_symbol = `PLUS
        ) ;

        let compare_return (kid1, atom1) (kid2_opt, atom2) =
          (* Both these kids should be constants. *)
          if Term.is_numeral kid1 then Some (
            let kid2 =
              match kid2_opt with
              | None -> Numeral.zero
              | Some k -> Term.numeral_of_term k
            in
            if Numeral.leq
                (Term.numeral_of_term kid1) kid2
            then atom1 else atom2
          ) else if Term.is_decimal kid1 then Some (
            let kid2 =
              match kid2_opt with
              | None -> Decimal.zero
              | Some k -> Term.decimal_of_term k
            in
            if Decimal.leq
                (Term.decimal_of_term kid1) kid2
            then atom1 else atom2
          ) else
            Format.asprintf "unexpected kid @[<h>%a@]" Term.pp_print_term kid1
            |> failwith
        in

        (* Checking if kids of lhs are the same modulo last one. *)
        let rec loop = function
          | [ kid1 ], [ kid2 ] ->
            compare_return (kid1, atom1) (Some kid2, atom2)
          | [ kid1 ], [] ->
            compare_return (kid1, atom1) (None, atom2)
          | [], [ kid2 ] ->
            compare_return (kid2, atom2) (None, atom1)
          | kid1 :: tail1, kid2 :: tail2 ->
            if kid1 != kid2 then None else loop (tail1, tail2)
          | _,_ ->
            Format.asprintf "unexpected atoms @[<h>%a and %a@]"
              Term.pp_print_term atom1 Term.pp_print_term atom2
            |> failwith
        in
        
        loop (Term.node_args_of_term lhs1, Term.node_args_of_term lhs2)
      )
    | _ ->
      Format.asprintf
        "unexpected atoms \"%a\" and \"%a\""
        Term.pp_print_term atom1
        Term.pp_print_term atom2
      |> failwith
  )

(* Simplifies the output of quantifier elimination to remove redundant
   atoms.

   /!\ Assumes all variables in the atoms have the same offset. This is the
   case for the ones produced by QE. *)
let simplify_cube = function
| head :: tail ->
  let rec loop mem prefix atom = function
    | atom' :: tail -> (
      match least_general_of atom atom' with
      | Some atom'' ->
        (* Format.printf
          "| discarding @[<h>%a@]@.| for @[<h>%a@]@."
          Term.pp_print_term (if atom == atom'' then atom' else atom)
          Term.pp_print_term atom'' ; *)
        loop mem prefix atom'' tail
      | None -> loop (atom' :: mem) prefix atom tail
    )
    | [] -> (
      match mem with
      | atom' :: tail -> loop [] (atom :: prefix) atom' tail
      | [] -> atom :: prefix
    )
  in
  loop [] [] head tail
| [] -> failwith "called with empty cube"

(* Enumeration type for the result of negating a term. Either the term was
   actually negated ([Negated term]) and yields [term], or it is necessary to
   descend further in the term ([Continue (sym, kids)]). *)
type negate_result =
| Negated of Term.t | Continue of Symbol.symbol * Term.t list

(* [negate_terms terms] goes through each term in [terms] and negates the
   arithmetic leaves. *)
let negate_terms =

  let rec negate_term term =
    if Term.is_numeral term then Negated (
      (* Extracting numeral. *)
      Term.numeral_of_term term
      (* Negating it. *)
      |> Numeral.(~-)
      (* Reconstructing term. *)
      |> Term.mk_num

    ) else if Term.is_decimal term then Negated (
      (* Extracting decimal. *)
      Term.decimal_of_term term
      (* Negating it. *)
      |> Decimal.(~-)
      (* Reconstructing term. *)
      |> Term.mk_dec

    ) else if Term.is_free_var term then Negated (
      (* Free variable negation. *)
      Term.mk_minus [ term ]

    ) else if Term.is_leaf term |> not then
      (* Extracting symbol and kids. *)
      let sym, kids =
        Term.node_symbol_of_term term, Term.node_args_of_term term
      in
      match Symbol.node_of_symbol sym, kids with
      (* Term is [- something]. *)
      | `MINUS, [ kid ] -> Negated kid
      (* Term is something else. *)
      | sym, _ -> Continue (sym, kids)

    else
      Format.asprintf "unexpected term @[<h>%a@]" Term.pp_print_term term
      |> failwith
  in

  (* Continuation is a list of triples: [sym, to_negate, negated] where [sym]
     is the symbol of the node, [to_negate] are terms not negated yet, and
     [negated] are the terms already negated in reverse order. *)
  let rec negate continuation term = match negate_term term with

    | Negated term' ->
      (* Format.printf
        "| rewrote @[<h>%a@]@.| to @[<h>%a@]@."
        Term.pp_print_term term Term.pp_print_term term' ; *)
      zip_up continuation term'

    | Continue (sym, kid :: kids) ->
      (* Format.printf "| going down @[<h>%a@]@." Term.pp_print_term term ; *)
      (* Augmenting continuation and looping. *)
      negate ( (sym, kids, []) :: continuation ) kid

  (* Attempts to zip up from a negated term and a continuation. *)
  and zip_up continuation term = match continuation with
    | (`TIMES, to_negate, negated) :: tail ->
      (* Format.printf "|   zip up (times) from @[<h>%a@]@."
        Term.pp_print_term term ; *)
      (* Multiplication, negating the first kid is enough. *)
      assert (negated = []) ;
      term :: to_negate
      |> Term.mk_app_of_symbol_node `TIMES
      |> zip_up tail
    | (sym, [], negated) :: tail ->
      (* Format.printf "|   zip up (no more kids) from @[<h>%a@]@."
        Term.pp_print_term term ; *)
      (* No more kids of [sym] to negate, zipping up. *)
      term :: negated
      |> List.rev
      |> Term.mk_app_of_symbol_node sym
      |> zip_up tail
    | (sym, kid :: to_negate, negated) :: tail ->
      (* Format.printf "|   negate from @[<h>%a@]@."
        Term.pp_print_term term ; *)
      (* There's some kids left to negate. *)
      negate ( (sym, to_negate, term :: negated) :: tail ) kid
    | [] ->
      (* Nothing left to do, we're done. *)
      term
  in

  (* Negating each term of the input list. *)
  negate [] |> List.map

(* Returns the convex cube from a QE result. More precisely, transforms
   `(not (eq whatever))` by evaluating `(< whatever)` and `(> whatever)` in the
   model. If the former it true, then it is rewritten as a `(> whatever')`. *)
let convexify sys model =
  let fail atom =
    Format.asprintf "unexpected atom \"%a\"" Term.pp_print_term atom
    |> failwith
  in
  let to_conv atom = match Term.destruct atom with
    | Term.T.App (sym, kids) -> (
      match Symbol.node_of_symbol sym, kids with
      | `NOT, [ kid ] -> (
        match Term.destruct kid with
        | Term.T.App (sym, kids) -> (
          match Symbol.node_of_symbol sym with
          | `EQ ->
            (* Creating inequalities to evaluate. *)
            let gt = Term.mk_gt kids in
            (* Evaluating `gt`. *)
            let gt_val =
              Eval.eval_term (TransSys.uf_defs sys) model gt
              |> Eval.bool_of_value
            in

            (* Format.printf "| rewriting %a@," Term.pp_print_term atom ; *)

            let out = if gt_val then gt else negate_terms kids |> Term.mk_gt in

            (* Format.printf "| new atom is %a@." Term.pp_print_term out ; *)
            out
          | _ -> fail atom
        )
      )
      (* Not a `NOT`, should be a convex atom. *)
      | _ -> atom
    )
    | _ ->
      Format.asprintf "unexpected atom \"%a\"" Term.pp_print_term atom
      |> failwith
  in

  List.map to_conv

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
    (* Format.printf "| model: @[<v>%a@]@," Model.pp_print_model model ; *)
    (* Term to extrapolate. *)
    let term =
      (TransSys.trans_of_bound sys Numeral.one) ::
      (TransSys.invars_of_bound sys Numeral.one) ::
      (TransSys.invars_of_bound sys Numeral.zero) ::
      (Term.bump_state Numeral.one src) :: []
      |> Term.mk_and
    in

    (* Format.printf "| term 4 qe: @[<v>%a@]@." Term.pp_print_term term ; *)

    (* Getting primed variables in the transition system. *)
    let vars = 
      Var.VarSet.elements
        (Term.vars_at_offset_of_term (Numeral.one) term) 
    in
    (* Generalizing. *)
    let cube =
      QE.generalize sys (TransSys.uf_defs sys) model vars term
      |> List.filter (fun lit ->
        match Term.var_offsets_of_term lit with
        | None, None -> false | _ -> true
      )
      (* |> fun cube ->
        Format.printf "| qe: @[<v>%a@]@."
          (pp_print_list Term.pp_print_term "@,") cube ;
        cube *)
      |> convexify sys model
      (* |> fun cube ->
        Format.printf "| convexified: @[<v>%a@]@."
          (pp_print_list Term.pp_print_term "@,") cube ;
        cube *)
      |> simplify_cube
    in
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
