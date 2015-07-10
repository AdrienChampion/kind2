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

type model = Model.t
type term = Term.t
type num = Numeral.t

(** A depth is just a numeral. *)
type depth = num

(** A [mode] is just its name. *)
type mode = string

(**
  A conjunction of modes. Several can be activated at the same time and
  represent different paths.
*)
type mode_conj = mode list

(**
  A [mode_path] stores the modes activated by the path in reverse order.
*)
type mode_path = mode_conj list

(**
  A [witness] is a model and a [mode_path].
*)
type witness = model * mode_path

(**
  Stores the witnesses and the reversed tree.
  Also stores a mode to term function to construct constraints to activate or
  block mode paths / conjunctions of modes.
*)
type t

(**
  Exception raised when [Top] is reached.
*)
exception TopReached of witness list

(**
  Creates a reversed partial tree. [mode_conj] is a conjunction of modes
  activable in the initial state. [mode_to_term] is the function mapping mode
  names to their term @0.
  Originally there are no witnesses, some initial state mode, and no modes
  explored.
*)
val mk_reved_tree: (string -> term) -> string list -> t

(**
  Returns the term encoding the path of modes represented by a tree.

  Used to check which modes can be activated to extend the path being currently
  explored.
*)
val path_of: t -> Term.t

(**
  Returns the term encoding the path of modes leading to the current node but
  blocking its mode conjunction and explored modes.

  Used when backtracking, to see if different modes can be activated at the
  current depth.
*)
val blocking_path_of: t -> Term.t

(**
  Depth of the current node of a tree.
*)
val depth_of: t -> num

(**
  Pushes a node on top of the current one, activating a mode conjunction.
*)
val push: t -> string list -> unit

(**
  Pops the current node.
*)
val pop: t -> unit

(**
  Adds a witness for the current node.

  Used when at maximal depth to store a witness.
*)
val add_witness: t -> model -> unit


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
