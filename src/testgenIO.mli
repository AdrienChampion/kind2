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


(** Stores IO things to log testcases to xml. *)
type t

(* [mk sys root name title] creates a new IO struct for system [sys], in
   directory [root]. [name] is an ident-like description of the testgen
   strategy and [title] is a more verbose description. *)
val mk: TransSys.t -> string -> string -> string -> t


(** Closes internal file descriptors. *)
val rm: t -> unit

(** The number of testcases generated. *)
val testcase_count: t -> int

(** [testcase_to_xml t modes model k] logs a test case of length [k]
    represented by model [model] and activating modes [modes] using the info
    in [t]. *)
val testcase_to_xml: t -> string list list -> Model.t -> Numeral.t -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
