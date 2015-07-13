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
  (* Directory to log the testcases in. *)
  dir: string ;
  (* XML class file. *)
  class_file: file ;
  (* Graph file. *)
  graph_file: file ;
}

let openfile path = Unix.openfile path [
  Unix.O_TRUNC ; Unix.O_WRONLY ; Unix.O_CREAT
] 0o640

let fmt_of_file file =
  Unix.out_channel_of_descr file |> Format.formatter_of_out_channel

(* Creates a new IO struct. *)
let mk sys root name title =
  (* |===| Testcases directory. *)
  let dir = Format.sprintf "%s/%s" root name in
  ( try if Sys.is_directory dir |> not
      then assert false else ()
    with e ->
      Unix.mkdir dir 0o740 ) ;

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
  { sys ; uid = 0 ; dir ;
    class_file = class_file ;
    graph_file = graph_file ; }


(* Closes internal file descriptors. *)
let rm { class_file ; graph_file } =
  (* |===| Finishing class file. *)
  let class_fmt = fmt_of_file class_file in
  Format.fprintf class_fmt "@.</data>@.@?" ;
  (* |===| Finishing graph file. *)
  let graph_fmt = fmt_of_file graph_file in
  Format.fprintf graph_fmt "}@.@?" ;
  Unix.close class_file ; Unix.close graph_file

(* The number of testcases generated. *)
let testcase_count { uid } = uid

(* Formatter for a testcase file. *)
let testcase_file ({uid ; dir} as t) =
  let name = Format.sprintf "testcase_%d" uid in
  let path = Format.sprintf "%s/%s.csv" dir name in
  t.uid <- uid + 1 ;
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
let testcase_to_xml t modes model k =
  Format.printf "testcase_to_xml@." ;

  (* |===| Logging testcase. *)
  Format.printf "  logging testcase@." ;
  let name, path, tc_file = testcase_file t in
  let tc_fmt = fmt_of_file tc_file in
  (* Logging test case. *)
  cex_to_inputs_csv tc_fmt t.sys model k ;
  (* Flushing. *)
  Format.fprintf tc_fmt "@?" ;
  (* Close file. *)
  Unix.close tc_file ;

  (* |===| Updating class file. *)
  Format.printf "  updating class file@." ;
  let class_fmt = fmt_of_file t.class_file in
  pp_print_tc class_fmt path name modes ;

  (* |===| Updating graph. *)
  Format.printf "  updating graph@." ;
  let graph_fmt = fmt_of_file t.graph_file in
  pp_print_model_path graph_fmt modes ;

  (* let class_fmt = fmt_of_file t.class_file in
  let graph_fmt = fmt_of_file t.graph_file in *)

  ()





(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
