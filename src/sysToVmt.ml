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

let name_of_sys sys =
  Sys.scope_of_trans_sys sys |> Format.asprintf "%a" Scope.pp_print_scope

let fmt_ufsym = UfSymbol.pp_print_uf_symbol
let fmt_sym = Symbol.pp_print_symbol
let fmt_svar = SVar.pp_print_state_var
let fmt_var fmt var =
  if Var.is_state_var_instance var then (
    let svar, off =
      Var.state_var_of_state_var_instance var,
      Var.offset_of_state_var_instance var
    in
    let pref =
      if Num.(off = zero) then "curr" else
      if Num.(off = one)  then "next" else
        Format.asprintf "unexpected offset %a in variable %a"
          Num.pp_print_numeral off Var.pp_print_var var
    in
    Format.fprintf fmt "(_ %s %a)" pref fmt_svar svar
  ) else (
    Var.pp_print_var fmt var
  )
let fmt_term = Term.pp_print_term_cstm fmt_var
let fmt_type = Type.pp_print_type
let fmt_list = pp_print_list

let invariant_name = "str_invariant"
let init_name = "init"
let trans_name = "trans"
let prop_name = "prop"


let rm_none =
  let rec filter_map pref = function
    | None :: tail -> filter_map pref tail
    | (Some kid) :: tail -> filter_map (kid :: pref) tail
    | _ -> List.rev pref
  in
  filter_map []

(** Removes all node calls from the first level of a conjunction.

Leaves the term untouched if it's not a conjunction. *)
let clean_predicate term =
  let term =
    Term.eval_t (
      fun flat kids ->
        let kids = rm_none kids in
        match flat with
        | Term.T.App ( sym, subs ) -> (
          match Symbol.node_of_symbol sym with
          (* Node call. *)
          | `UF _ -> None
          (* This function only changes the boolean structure of the term.
          Hence the only special treatment is on bool operators. *)
          | `AND -> Some (
            match kids with
            | [] -> Term.t_true
            | _ -> Term.mk_and kids
          )
          | `OR -> Some (
            match kids with
            | [] -> Term.t_true
            | _ -> Term.mk_or kids
          )
          (* Other operators, should not change. *)
          | _ -> Some (
            assert ( List.length subs = List.length kids ) ;
            Term.mk_app sym kids
          )
        )
        | Term.T.Var _
        | Term.T.Const _ -> Some (
          Term.construct flat
        )
        | Term.T.Attr (_, attr) -> failwith "term attributes not supported"
    ) term
  in
  match term with
  | None -> Term.t_true
  | Some t -> t
(*   try (
    match (
      Term.node_symbol_of_term term |> Symbol.node_of_symbol,
      Term.node_args_of_term term
    ) with
    | `AND, kids -> (
      let kids =
        kids |> List.filter (
          fun kid -> try (
            match (
              Term.node_symbol_of_term kid |> Symbol.node_of_symbol
            ) with
            | `UF s -> false
            | _ -> true
          ) with invalid_arg -> true
        )
      in
      match kids with
      | [] -> Term.t_true
      | [ kid ] -> kid
      | _ -> Term.mk_and kids
    )
    | _ -> term
  ) with
  (** Not a conjunction. *)
  | invalid_arg -> term *)

let svar_at k svar = Var.mk_state_var_instance svar k |> Term.mk_var

let fmt_svar_as_arg fmt svar =
  let typ = SVar.type_of_state_var svar in
  Format.fprintf fmt "(%a %a)" fmt_svar svar fmt_type typ

let declare_const fmt const =
  let typ = SVar.type_of_state_var const in
  Format.fprintf fmt "(declare-fun %a () %a)@."
    fmt_svar const fmt_type typ

let fmt_instance fmt (sys, { Sys.pos ; Sys.map_up }) =
  let name = name_of_sys sys in
  let actual =
    Sys.state_vars sys
    |> List.fold_left (
      fun acc svar ->
        if SVar.is_const svar then acc else (
          try
            SVar.StateVarMap.find svar map_up
          with Not_found ->
            Event.log L_fatal
              "[sys_to_vmt] svar %a not found in map_up of instance of %s (%a)" fmt_svar svar name pp_print_pos pos ;
            exit 2
        ) :: acc
    ) []
    |> List.rev
  in
  Format.fprintf fmt "(%s %a)"
    name
    (pp_print_list
      (fun fmt -> Format.fprintf fmt "(_ curr %a)" fmt_svar)
      " "
    ) actual

let fmt_instances fmt (sys, instances) =
  instances
  |> List.map (fun instance -> sys, instance)
  |> Format.fprintf fmt "@[<v>%a@]"
    (pp_print_list fmt_instance "@ ")

let props_of_sys sys =
  let name = name_of_sys sys in
  Sys.props_list_of_bound sys zero
  |> List.fold_left (
    fun (cnt, acc) (_, prop_term) ->
      let prop_name =
        Format.sprintf "%s_prop_%d" name cnt
      in
      cnt + 1, (prop_name, prop_term) :: acc
  ) (1, [])
  |> snd
  |> List.rev

let fmt_sys fmt sys =
  let consts, svars = Sys.state_vars sys |> List.partition SVar.is_const in
  let init = Sys.init_of_bound sys zero |> clean_predicate in
  let trans = Sys.trans_of_bound sys one |> clean_predicate in
  let props = props_of_sys sys in
  let name = name_of_sys sys in

  ( match consts with
    | [] -> ()
    | _ ->
      Format.fprintf fmt "\
          ;; Constants for system '%s'.@.\
          %a@.@.\
        "
        name
        (pp_print_list declare_const "@.") consts
  ) ;

  (* System declaration. *)
  Format.fprintf fmt "\
      (define-sys@   \
        @[<v>\
          %s (@   \
            @[<v>%a@]@ \
          ) (@   \
            @[<v>\
              %a\
            @]\
          @ \
          ) (@   \
            @[<v>\
              %a\
            @]\
          @ \
          ) (@   \
            @[<v>\
              %a\
            @]\
          @ \
          )\
        @]\
        @.\
      )@.\
    " name
    (pp_print_list fmt_svar_as_arg "@ ") svars
    fmt_term init
    fmt_term trans
    (pp_print_list fmt_instances "@ ")
    (Sys.get_subsystem_instances sys) ;

  (* Property declarations. *)
  props |> List.fold_left (
    fun cnt (_, prop_term) ->
      Format.fprintf fmt
        "(define-prop@.  %s_prop_%d@.  %s@.  %a@.)@."
        name cnt name fmt_term prop_term ;
      cnt + 1
  ) 1 ;

  ()

  (* Format.fprintf fmt "%a" *)

let fmt_sys_vmt fmt sys =
  (* Declaring subsystems. *)
  sys |> Sys.iter_subsystems (
    Format.fprintf fmt "%a@.@." fmt_sys
  ) ;
  Format.fprintf fmt "@.@." ;

  (* Verify query. *)
  let props = props_of_sys sys |> List.map fst in
  let name = name_of_sys sys in
  Format.fprintf fmt "(verify@.  %s (@.    @[<v>%a@]@.  )@.)@.@."
    name (pp_print_list Format.pp_print_string "@ ") props

  (* (** Declaring subsystems. *)
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
        fmt_term term ;
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
  Format.fprintf fmt "(check-synth)@." *)

(*
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End:
*)
