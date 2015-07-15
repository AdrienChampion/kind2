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

module N = LustreNode

type sys = TransSys.t
type svar = StateVar.t
type actlit = UfSymbol.t
type term = Term.t
type model = Model.t
type values = (Term.t * Term.t) list
type k = Numeral.t

type file = Unix.file_descr


(* Stores IO things to log testcases to xml. *)
type t = {
  (* System. *)
  sys: sys ;
  (* Counter for test case uid. *)
  mutable uid: int ;
  (* Counter for error uid. *)
  mutable euid: int ;
  (* Directory to log the testcases in. *)
  dir: string ;
  (* XML class file. *)
  class_file: file ;
  (* Graph file. *)
  graph_file: file ;
  (* Error dir. *)
  edir: string ;
  (* Error file. *)
  mutable error_file: file option ;
}

let openfile path = Unix.openfile path [
  Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT
] 0o640

let mk_dir dir =
  try Unix.mkdir dir 0o740 with Unix.Unix_error(Unix.EEXIST, _, _) -> ()

let fmt_of_file file =
  Unix.out_channel_of_descr file |> Format.formatter_of_out_channel

(* Creates a new IO struct. *)
let mk sys root name title =
  (* |===| Testcases directory. *)
  let dir = Format.sprintf "%s/%s" root name in
  let edir = Format.sprintf "%s/errors" dir in
  mk_dir dir ;

  (* |===| XML class file. *)
  let class_file =
    Format.sprintf "%s.xml" dir |> openfile
  in
  let class_fmt = fmt_of_file class_file in
  Format.fprintf class_fmt
    "<?xml version=\"1.0\"?>@.\
     <data system=\"%s\" name=\"%s\">@.@.@?"
    (TransSys.get_scope sys |> String.concat ".")
    title ;

  (* |===| Graph file. *)
  let graph_file =
    Format.sprintf "%s.dot" dir |> openfile
  in
  let graph_fmt = fmt_of_file graph_file in
  Format.fprintf graph_fmt "strict digraph mode_graph {@.@.@?" ;

  (* Building result. *)
  { sys ; uid = 0 ; euid = 0 ; dir ;
    class_file = class_file ;
    graph_file = graph_file ;
    edir ; error_file = None ; }

(* Initialization for error dir and file. *)
let init_error ({ sys ; dir ; edir } as t) =
  ( if t.error_file <> None then
      failwith "init_error called with existing error file" ) ;
  mk_dir edir ;
  let error_file = Format.sprintf "%s-errors.xml" dir |> openfile in
  let error_fmt = fmt_of_file error_file in
  Format.fprintf error_fmt
    "<?xml version=\"1.0\"?>@.\
     <data system=\"%s\">@.@.@?"
    (TransSys.get_scope sys |> String.concat ".") ;

  t.error_file <- Some error_file


(* Closes internal file descriptors. *)
let rm { class_file ; graph_file ; error_file } =
  (* |===| Finishing class file. *)
  let class_fmt = fmt_of_file class_file in
  Format.fprintf class_fmt "@.</data>@.@?" ;
  (* |===| Finishing graph file. *)
  let graph_fmt = fmt_of_file graph_file in
  Format.fprintf graph_fmt "}@.@?" ;
  Unix.close class_file ; Unix.close graph_file ;
  (* |===| Finishing error file. *)
  ( match error_file with
    | None -> ()
    | Some error_file ->
      let error_fmt = fmt_of_file error_file in
      Format.fprintf error_fmt "@.</data>@.@?" ;
      Unix.close error_file ) ;
  ()

(* The number of testcases generated. *)
let testcase_count { uid } = uid

(* The number of errors logged. *)
let error_count { euid } = euid

(* Descriptor for a testcase file. *)
let testcase_csv ({uid ; dir} as t) =
  let name = Format.sprintf "testcase_%d" uid in
  let path = Format.sprintf "%s/%s.csv" dir name in
  t.uid <- uid + 1 ;
  name, path, openfile path

(* Descriptor for an error file. *)
let error_csv ({euid ; edir} as t) =
  let name = Format.sprintf "error_%d" euid in
  let path = Format.sprintf "%s/%s.csv" edir name in
  t.euid <- euid + 1 ;
  name, path, openfile path

(* Converts a model to the system's input values in csv. *)
let cex_to_inputs_csv fmt sys cex k = match TransSys.get_source sys with
  | TransSys.Lustre nodes ->
    let path =
      Model.path_from_model (TransSys.state_vars sys) cex k
    in
    Format.fprintf fmt
      "@[<v>%a@]"
      (LustrePath.pp_print_path_inputs_csv nodes true) path
  (* Not supporting non lustre sources. *)
  | _ -> assert false

(* Pretty printer for a testcase in xml. *)
let pp_print_tc fmt path name modes =
  let rec loop cpt = function
    | modes :: tail ->
      Format.fprintf fmt
        "    at step %d, activates @[<v>%a@]@." cpt
        (pp_print_list Format.pp_print_string " and ")
        modes ;
      loop (cpt + 1) tail
    | [] -> ()
  in
  Format.fprintf fmt
    "  <testcase path=\"%s\" name=\"%s\" format=\"csv\">@." path name ;
  List.rev modes |> loop 0 ;
  Format.fprintf fmt "  </testcase>@.@."

(* Pretty printer for a deadlock in xml. *)
let pp_print_deadlock fmt path name modes =
  let rec loop cpt = function
    | modes :: tail ->
      Format.fprintf fmt
        "    at step %d, activates @[<v>%a@]@." cpt
        (pp_print_list Format.pp_print_string " and ")
        modes ;
      loop (cpt + 1) tail
    | [] -> Format.fprintf fmt "    deadlock reached@."
  in
  Format.fprintf fmt
    "  <deadlock path=\"%s\" name=\"%s\" format=\"csv\">@." path name ;
  List.rev modes |> loop 0 ;
  Format.fprintf fmt "  </deadlock>@.@."

(* Pretty printer for a model path in dot. *)
let pp_print_model_path fmt path =
  let rec loop cpt = function
    | modes :: modes' :: tail ->
      Format.fprintf fmt "  %a_%d -> %a_%d ;@.@?"
        (pp_print_list Format.pp_print_string "__") modes cpt
        (pp_print_list Format.pp_print_string "__") modes' (cpt + 1) ;
      loop (cpt + 1) (modes' :: tail)
    | _ -> Format.fprintf fmt "@,@?"
  in
  List.rev path |> loop 0

(* Logs a test case. *)
let log_testcase t modes model k =
  Format.printf "  log_testcase@." ;

  (* |===| Logging testcase. *)
  Format.printf "    logging testcase@." ;
  let name, path, tc_file = testcase_csv t in
  let tc_fmt = fmt_of_file tc_file in
  (* Logging test case. *)
  cex_to_inputs_csv tc_fmt t.sys model k ;
  (* Flushing. *)
  Format.fprintf tc_fmt "@?" ;
  (* Close file. *)
  Unix.close tc_file ;

  (* |===| Updating class file. *)
  Format.printf "    updating class file@." ;
  let class_fmt = fmt_of_file t.class_file in
  pp_print_tc class_fmt path name modes ;

  (* |===| Updating graph. *)
  Format.printf "    updating graph@." ;
  let graph_fmt = fmt_of_file t.graph_file in
  pp_print_model_path graph_fmt modes ;

  ()

(* Logs a test case. *)
let rec log_deadlock t modes model k =
  match t.error_file with
  | None -> init_error t ; log_deadlock t modes model k
  | Some error_file ->
    Format.printf "  log_deadlock@." ;

    (* |===| Logging error. *)
    Format.printf "    logging deadlock@." ;
    let name, path, e_file = error_csv t in
    let e_fmt = fmt_of_file e_file in
    (* Logging test case. *)
    cex_to_inputs_csv e_fmt t.sys model k ;
    (* Flushing. *)
    Format.fprintf e_fmt "@?" ;
    (* Close file. *)
    Unix.close e_file ;

    (* |===| Updating class file. *)
    Format.printf "    updating error file@." ;
    let error_fmt = fmt_of_file error_file in
    pp_print_deadlock error_fmt path name modes ;

    ()


(* |===| Oracle generation. *)

(* Generates an oracle for the top system of [sys]. The inputs will be the
   inputs and outputs of [sys]. [terms] is a list of
   [LustreIdent.t * LustreExpr.t], used as outputs for the oracle. The
   [LustreIdent.t] is the name of the output and will be defined to be equal to
   its corresponding expression.
   The oracle will be created in a folder in [root].

   Returns the path to the oracle. *)
let generate_oracles sys root terms =
  let oracle_dir = Format.sprintf "%s/oracle" root in
  mk_dir oracle_dir ;
  let oracle_name sys = Format.asprintf
    "%a_oracle" (LustreIdent.pp_print_ident false) sys.N.name
  in
  (* Extracting lustre nodes. *)
  let nodes = match TransSys.get_source sys with
    | TransSys.Lustre nodes -> nodes
    | TransSys.Native -> assert false
  in
  let oracle_path =
    List.rev nodes |> List.hd |> oracle_name
    |> Format.sprintf "%s/%s.lus" oracle_dir
  in

  let (top, subs) =
    let rec last_rev_tail acc = function
      | [ h ] -> (h, acc)
      | h :: t -> last_rev_tail (h :: acc) t
      | [] -> assert false
    in
    last_rev_tail [] nodes
  in

  let oracle_ident =
    oracle_name top |> LustreIdent.mk_string_ident
  in

  let oracle_inputs = top.N.inputs @ top.N.outputs in

  let oracle_outputs, oracle_out_equations =
    terms
    |> List.fold_left
        ( fun (out,eqs) (id,expr) ->
            let sv =
              LustreExpr.mk_state_var_of_ident
                (LustreIdent.index_of_ident id)
                id
                (Type.mk_type Type.Bool)
            in
            (sv, LustreIdent.index_of_ident id) :: out,
            (sv, expr) :: eqs )
        ([],[])
    |> fun (out,eqs) -> List.rev out, List.rev eqs
  in

  let oracle_out_svs = List.map (fun (sv,_) -> sv) oracle_outputs in

  let filtered_top_eqs =
    top.N.equations
    |> List.filter (fun (sv,_) ->
      oracle_inputs
      |> List.exists (fun (sv',_) -> StateVar.equal_state_vars sv sv')
      |> not
    )
  in

  let oracle: N.t = {
    N.name = oracle_ident ;
    N.inputs = oracle_inputs ;
    N.oracles = top.N.oracles ;
    N.outputs = oracle_outputs ;
    N.observers = [] ; (*top.N.observers ;*)
    N.locals = top.N.locals ;
    N.equations = oracle_out_equations @ filtered_top_eqs ;
    N.calls = top.N.calls ;
    N.asserts = [] ;
    N.props = [] ;
    N.contract_spec = None ;
    N.is_main = true ;
    N.output_input_dep = [] ;
    N.fresh_state_var_index = top.N.fresh_state_var_index ;
    N.fresh_oracle_index = top.N.fresh_oracle_index ;
    N.state_var_oracle_map = top.N.state_var_oracle_map ;
    N.expr_state_var_map = top.N.expr_state_var_map ;
  } in

  let sliced =
    N.reduce_to_coi (oracle :: subs) oracle_ident oracle_out_svs
  in

  Format.printf "Writing oracle to %s@." oracle_path ;

  let file = openfile oracle_path in

  let out_fmt = fmt_of_file file in

  Format.fprintf
    out_fmt "%a@?"
    (pp_print_list
      (N.pp_print_node ~no_subrange:true true)
      "@.@.")
    sliced ;

  Unix.close file ;

  oracle_path


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
