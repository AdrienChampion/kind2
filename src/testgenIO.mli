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

(** Creates a new directory if it does not yet exist. *)
val mk_dir: string -> unit


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

(** The number of errors generated. *)
val error_count: t -> int

(** [log_testcase t modes model k] logs a test case of length [k]
    represented by model [model] and activating modes [modes] using the info
    in [t]. *)
val log_testcase: t -> string list list -> Model.t -> Numeral.t -> unit

(** [log_deadlock t modes model k] logs a deadlock trace of length [k]
    represented by model [model] and activating modes [modes] using the info
    in [t]. *)
val log_deadlock: t -> string list list -> Model.t -> Numeral.t -> unit

(* Generates an oracle for the top system of [sys]. The inputs will be the
   inputs and outputs of [sys]. [terms] is a list of [string * Term.t] of
   outputs to use for the oracle. The [string] is used to name the output and
   will be defined to be equal to its term.
   The oracle will be created in a folder in [root].

   Returns the path to the oracle. *)
val generate_oracles: TransSys.t -> string -> (
  (LustreIdent.t * LustreExpr.t) list
) -> string



(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
