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

module Sys = TransSys

type sys = Sys.t

(* A mode is the string representation of the mode and its term@0. *)
type mode = string * Term.t

(* A global mode and the list of modes. *)
type modes = (mode option) * (mode list)

(* A system and its modes. *)
type sys_modes = sys * (modes list)

(* The modes for some system and its subsystems. *)
type t = modes * (sys_modes list)

(* Pretty printer for [mode]. *)
let pp_print_mode fmt (name, term) =
  Format.fprintf fmt "%s (%a)" name Term.pp_print_term term

(* Pretty printer for [modes]. *)
let pp_print_modes fmt (g_opt, m_list) =
  Format.fprintf fmt
    "@[<v>- %a@ - [ @[<v>%a@] ]@]"
    ( fun fmt -> function
      | None -> Format.fprintf fmt "none"
      | Some mode -> pp_print_mode fmt mode )
    g_opt
    (pp_print_list pp_print_mode "@ ")
    m_list

(* Pretty printer for [sys_modes]. *)
let pp_print_sys_modes fmt (sys, modes) =
  Format.fprintf fmt "%s: @[<v>* %a@]"
    (Sys.get_name sys)
    (pp_print_list pp_print_modes "@ * ") modes

(* Pretty printer for [t]. *)
let pp_print_modes fmt (top, subs) =
  Format.fprintf fmt "@[<v>top level:@   %a@ subsystems:@   @[<v>%a@]@]"
    pp_print_modes top (pp_print_list pp_print_sys_modes "@ ") subs

(* Returns the term corresponding to a state variable at 0. *)
let sv_at_0 sv = Var.mk_state_var_instance sv Numeral.zero |> Term.mk_var

(* Returns the modes of a system as something of type [modes]. *)
let modes_of_sys sys =
  match
    Sys.get_contracts sys |> List.fold_left (fun (g,m) (_, sv, name) ->
      let pair = ( name, sv_at_0 sv ) in
      match Sys.contract_is_global sys name with
      | Some false -> g, pair :: m
      | Some true  -> pair :: g, m
      | None -> failwith "unreachable 1"
    ) ([], [])
  with
  | [], [] -> None, []
  | [ global ], modes -> Some global, modes
  | _, _ ->
    Format.sprintf
      "unsupported: system %s has more than one global mode"
      (Sys.get_name sys)
    |> failwith

(* The modes corresponding to a system and its subsystems. *)
let modes_of sys =
  Format.printf "modes_of@." ;
  (* Retrieving top modes. *)
  let top = modes_of_sys sys in
  (* Retrieving subsystems' modes. *)
  let subs =
    Sys.get_subsystems sys |> List.fold_left (fun subs subsys ->
      match modes_of_sys subsys with
      | None, [] -> subs (* No contract, ignoring. We might want to go down the
                            hierarchy in this case. *)
      | global, modes -> (* Subsystem has contracts, instantiating. *)
        (* Builds the list of instantiated modes for each call to [subsys] in
           [sys]. Accum is an option of a list the length of which is the
           number of calls to [subsys] in [sys]. *)
        let rec instantiate_modes accum = function
          | (name,term) :: tail ->
            let instantiated =
              Sys.instantiate_terms_for_sys subsys [term] sys
              |> List.map (function
                (* Building a list so that everything works fine if
                   [accum = None]. *)
                | [term] -> [ name, term ]
                | _ -> failwith "unreachable 2"
              )
            in
            instantiate_modes ( Some
              ( match accum with
                | None -> instantiated
                | Some modes ->
                  (* Doing a [map2] so that instantiations match. *)
                  modes |> List.map2 (fun l l' -> l @ l') instantiated )
            ) tail
          | [] ->
            ( match accum with
              | Some res -> res | None -> [] )
        in
        let instantiated_modes = instantiate_modes None modes in
        (
          subsys,
          match global, instantiated_modes with
          (* No global, adding node to each instantiation. *)
          | None, _ -> instantiated_modes |> List.map (fun ms -> None, ms)
          (* Global mode, instantiating. *)
          | Some (name, term), [] ->
            Sys.instantiate_terms_for_sys subsys [term] sys
            |> List.map (function
              | [ term ] -> Some (name, term), []
              | _ -> failwith "unreachable 3"
            )
          | Some (name, term), _ ->
            Sys.instantiate_terms_for_sys subsys [term] sys
            (* [map2] with instantiated modes. *)
            |> List.map2 (fun modes -> function
              | [ term ] -> Some (name, term), modes
              | _ -> failwith "unreachable 4"
            ) instantiated_modes
        ) :: subs
    ) []
  in
  top, subs


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
  
