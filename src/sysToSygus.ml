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


open Format
open Lib

module Sys = TransSys
module Num = Numeral
module SVar = StateVar

let zero = Num.zero
let one = Num.one

let fmt_ufsym = UfSymbol.pp_print_uf_symbol
let fmt_sym = Symbol.pp_print_symbol
let fmt_svar = SVar.pp_print_state_var
let fmt_var fmt var =
  if Var.is_state_var_instance var then (
    let svar, off =
      Var.state_var_of_state_var_instance var,
      Var.offset_of_state_var_instance var
    in
    let off =
      if Num.(off = zero) then "" else
      if Num.(off = one)  then "!" else
        Format.asprintf "unexpected offset %a in variable %a"
          Num.pp_print_numeral off Var.pp_print_var var
    in
    Format.fprintf fmt "%a%s" fmt_svar svar off
  ) else (
    Var.pp_print_var fmt var
  )
let fmt_term = Term.pp_print_term_cstm fmt_var
let fmt_term_vanilla = Term.pp_print_term
let fmt_type = Type.pp_print_type
let fmt_list = pp_print_list

let invariant_name = "str_invariant"
let init_name = "init"
let trans_name = "trans"
let prop_name = "prop"

let svar_at k svar = Var.mk_state_var_instance svar k |> Term.mk_var

let fmt_svar_as_arg n fmt svar =
  let typ = SVar.type_of_state_var svar in
  let var = Var.mk_state_var_instance svar n |> Term.mk_var in
  Format.fprintf fmt "(%a %a)" fmt_term var fmt_type typ

let synth_inv fmt svars =
  Format.fprintf fmt
    "@[<v>(synth-inv %s(@   @[<v>%a@]@ ))@.@]"
    invariant_name
    (fmt_list (fmt_svar_as_arg zero) "@ ")
    svars

let declare_svar fmt svar =
  let typ = SVar.type_of_state_var svar in
  Format.fprintf fmt "(declare-primed-var %a %a)@."
    fmt_svar svar fmt_type typ

let fmt_sys_sygus fmt sys =
  let consts, svars = Sys.state_vars sys |> List.partition SVar.is_const in
  let all_svars = consts @ svars in
  let init = Sys.init_of_bound sys zero in
  let trans =
    let trans = Sys.trans_of_bound sys one in
    match consts with
    | [] -> trans
    | _ -> trans :: (
      consts |> List.map (fun svar ->
        Term.mk_eq [ svar_at one svar ; svar_at zero svar ]
      )
    ) |> Term.mk_and
  in
  Event.log L_info "  building property (post-condition)..." ;
  let prop =
    Sys.props_list_of_bound sys zero
    |> List.rev
    |> List.fold_left (
      fun acc (_, t) -> t :: acc
    ) []
    |> Term.mk_and
  in

  Event.log L_info "  set logic..." ;

  (** Setting logic. *)
  let _ =
    let rec logic_loop int real = function
      | [] -> int, real
      | svar :: tail ->
        let int, real =
          match SVar.type_of_state_var svar |> Type.node_of_type with
          | Type.Int -> true, real
          | Type.IntRange _ -> true, real
          | Type.Real -> int, true
          | Type.Bool -> int, real
          | t ->
            Log.log L_fatal
              "Cannot generate sygus system, unsupported type %a"
              Type.pp_print_type_node t ;
            exit 2
        in
        if int && real then true, true else logic_loop int real tail
    in
    let int, real =
      Sys.uf_defs sys
      |> List.fold_left (
        fun acc (_, (vars, _)) ->
          List.rev_append (
            vars |> List.map Var.state_var_of_state_var_instance
          ) acc
      ) (
        sys |> Sys.fold_subsystems(
          fun acc sys -> Sys.state_vars sys @ acc
        ) []
      )
      |> logic_loop false false
    in
    if int || real then
      Format.fprintf fmt "(set-logic L%s%sA)@.@."
        (if int then "I" else "") (if real then "R" else "")
    else
      Format.fprintf fmt "(set-logic SAT)@.@."
  in

  (** Declaring subsystems. *)
  Event.log L_info "  declaring subsystems..." ;
  Sys.uf_defs sys |> List.iter (
    fun (sym, (vars, term)) ->
      Format.fprintf fmt
        "(define-fun@   \
          @[<v>\
            %a (@   \
              @[<v>%a@]@ \
            ) Bool@ \
            @ \
            %a\
          @]@ \
        )@."
        fmt_ufsym sym
        (pp_print_list
          (fun fmt var ->
            Format.fprintf fmt "(%a %a)"
              Var.pp_print_var var
              fmt_type (Var.type_of_var var)
          )
          "@ "
        ) vars
        fmt_term_vanilla term ;
      Format.fprintf fmt "@."
  ) ;
  Format.fprintf fmt "@.@." ;

  (** Declaring invariant to synthesize. *)
  Event.log L_info "  declaring invariant..." ;
  Format.fprintf fmt "%a@." synth_inv all_svars ;

  (** Declaring constants. *)
  Event.log L_info "  declaring constants..." ;
  consts |> List.iter (
    fun svar ->
      let typ = SVar.type_of_state_var svar in
      Format.fprintf fmt
        "(declare-var %a %a)@." fmt_svar svar fmt_type typ
  ) ;
  Format.fprintf fmt "@." ;

  (** Declaring state variables. *)
  Event.log L_info "  declaring state variables..." ;
  svars |> List.iter (declare_svar fmt) ;
  Format.fprintf fmt "@." ;

  (** Declaring "pre-condition". *)
  Event.log L_info "  declaring init (pre-condition)..." ;
  Format.fprintf fmt
    "@[<v>\
      (define-fun@   \
        @[<v>%s (@   \
          @[<v>\
            %a\
          @]@ \
        ) Bool@ @ \
        %a\
        @]@ \
      )\
    @]@.@."
    init_name
    (fmt_list (fmt_svar_as_arg zero) "@ ") all_svars
    fmt_term init ;

  (** Declaring transition relation. *)
  Event.log L_info "  declaring transition relation..." ;
  Format.fprintf fmt
    "@[<v>\
      (define-fun@   \
        @[<v>%s (@   \
          @[<v>\
            @ \
            ;; Constants.@ \
            %a@ \
            @ \
            ;; Current state.@ \
            %a@ \
            @ \
            ;; Next state.@ \
            %a\
          @]@ @ \
        ) Bool@ @ \
        %a\
        @]@ \
      )\
    @]@.@."
    trans_name
    (fmt_list (fmt_svar_as_arg zero) "@ ") consts
    (fmt_list (fmt_svar_as_arg zero) "@ ") svars
    (fmt_list (fmt_svar_as_arg one) "@ ") svars
    fmt_term trans ;

  (** Declaring "post-condition". *)
  Event.log L_info "  declaring property (post-condition)..." ;
  Format.fprintf fmt
    "@[<v>\
      (define-fun@   \
        @[<v>%s (@   \
          @[<v>\
            %a\
          @]@ \
        ) Bool@ @ \
        %a\
        @]@ \
      )\
    @]@.@."
    prop_name
    (fmt_list (fmt_svar_as_arg zero) "@ ") all_svars
    fmt_term prop ;

  (** Defining "inv-constraint". *)
  Event.log L_info "  defining invariant constraint..." ;
  Format.fprintf fmt
    "(inv-constraint %s %s %s %s)@.@."
    invariant_name init_name trans_name prop_name ;

  (** Query. *)
  Event.log L_info "  query..." ;
  Format.fprintf fmt "(check-synth)@."

(*
(** Rewrites the state variables of a sygus file in a legal format. *)
let sed_file file =
  let suf = ".bak" in
  let bak = Format.sprintf "%s%s" file suf in
  (* Sed command to rewrite [@0] and [@1]. *)
  (* [
    "-i.bak" ;
    "-e" ; "\"s:@0::g\"" ;
    "-e" ; "\"s:@1:':g\"" ;
    file
  ]
  |> Array.of_list
  |> Unix.execv "sed" ; *)
  Unix.system (
    Format.sprintf "sed -i.bak -e \"s:@0::g\" -e \"s:@1:':g\" %s" file
  ) |> ignore ;

  (* Remove backup. *)
  Unix.system (
    Format.sprintf "rm %s" bak
  ) |> ignore
*)

(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
