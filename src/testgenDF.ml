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

module Solver = TestgenSolver
module Tree = TestgenTree
module Sys = TransSys
module Num = Numeral


(* Reference to the solver for clean exit. *)
let solver_ref = ref None

(* Destroys the solver reference if any. *)
let on_exit _ =
  match !solver_ref with
  | None -> ()
  | Some solver -> Solver.rm solver

let get_model = SMTSolver.get_model

let unit_of _ = ()

let active_modes_of_map map =
  List.fold_left (fun modes (m,v) ->
    if v == Term.t_true then m :: modes else modes
  ) [] map
  |> fun active ->
    Format.printf "  active: @[<v>%a@]@."
      (pp_print_list Format.pp_print_string "@,") active ;
    active

let forward solver tree modes contract_term =
  let rec loop () =
    Format.printf "Tree: %a@." Tree.pp_print_tree tree ;
    let k = Tree.depth_of tree |> Num.succ in
    Format.printf "at %a@." Num.pp_print_numeral k ;
    let modes = modes |> List.map (fun (n,t) -> n, Term.bump_state k t) in
    let contract_term = Term.bump_state k contract_term in
    let mode_path = Term.mk_and [ Tree.path_of tree ; contract_term ] in

    if Flags.testgen_len () = Num.to_int k then
      (* We need the model. *)
      ( match Solver.checksat solver k mode_path [] modes get_model with
        | Some (map,model) ->
          (* Extracting modes activated @k by the model. *)
          active_modes_of_map map |> Tree.push tree ;
          Tree.add_witness tree model
        | None -> () )
    else
      (* Model is not needed. *)
      ( match Solver.checksat solver k mode_path [] modes unit_of with
        | Some (map,()) ->
          (* Extracting modes activated @k by the model. *)
          active_modes_of_map map |> Tree.push tree ;
          loop ()
        | None -> () )
  in
  loop ()



(* Entry point. *)
let main sys =

  (* Creating solver. *)
  let solver = Solver.mk sys in
  (* Memorizing solver for clean exit. *)
  solver_ref := Some solver ;

  (* Getting global contracts and modes association lists. *)
  let global, modes =
    Sys.get_contracts sys
    |> List.fold_left (fun (g,m) (_, sv, name) ->
      let pair =
        name, Var.mk_state_var_instance sv Numeral.zero |> Term.mk_var
      in
      match Sys.contract_is_global sys name with
      | Some true -> (pair :: g), m
      | Some false -> g, (pair ::m)
      | None -> failwith "unreachable"
    ) ([],[])
  in

  Format.printf
    "globals: @[<v>%a@]@.modes: @[<v>%a@]@."
    (pp_print_list (fun ppf (n,t) ->
        Format.fprintf ppf "%s -> %a" n Term.pp_print_term t
      ) "@,"
    ) global
    (pp_print_list (fun ppf (n,t) ->
        Format.fprintf ppf "%s -> %a" n Term.pp_print_term t
      ) "@,"
    ) modes ;

  let global_terms = global |> List.map snd in
  let mode_terms = modes |> List.map snd in

  let mode_term =
    (mode_terms |> Term.mk_or) :: global_terms |> Term.mk_and
  in

  Format.printf "checking init@." ;

  let init_modes =
    match
      Solver.checksat
        solver Numeral.zero mode_term [] modes unit_of
    with
    | None -> failwith "no mode activable in init"
    | Some (map, ()) -> active_modes_of_map map
  in

  let tree =
    Tree.mk (fun name -> List.assoc name modes) init_modes
  in

  Format.printf "depth is %a@." Num.pp_print_numeral (Tree.depth_of tree) ;

  forward solver tree modes mode_term ;

  Format.printf "Tree: %a@." Tree.pp_print_tree tree ;

  ()

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
