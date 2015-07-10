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

module Num = Numeral

type model = Model.t
type term = Term.t
type num = Num.t

(* A depth is just a numeral. *)
type depth = num

(* A [mode] is just its name. *)
type mode = string

(*
  A conjunction of modes. Several can be activated at the same time and
  represent different paths.
*)
type mode_conj = mode list

(*
  A [mode_path] stores the modes activated by the path in reverse order.
*)
type mode_path = mode_conj list

(*
  A [witness] is a model and a [mode_path].
*)
type witness = model * mode_path

(*
  Reversed partial tree for depth first search. Stores the activable modes at
  k and the witnesses for each path. The tree is partial because the witnesses
  for subtrees are collapsed into a single [Witnesses] leaf. The tree is
  reversed because the entry point is the current depth, the last element is
  the root.

  The idea is that when hitting the maximal depth during the exploration of the
  tree of activable modes, a witness is generated. This witness is propagated
  upward the reverse partial tree when backtracking.
*)

(*
  The adt for a reversed partial tree. Does not store witnesses.
*)
type rev_tree_adt =
(*
  The root of the tree, i.e. the top most element here since the tree is
  reversed.
*)
| Top
(*
  A node is its depth,  the node it comes from, the mode it corresponds to, and
  the mode conjunctions already explored from this node.
*)
| Node of depth * rev_tree_adt * mode_conj * (mode_conj list)

(*
  Stores the witnesses and the reversed tree.
  Also stores a mode to term function to construct constraints to activate or
  block mode paths / conjunctions of modes.
*)
type t = {
  mode_to_term: mode -> term ;
  mutable ws: witness list ;
  mutable tree: rev_tree_adt ;
}

(*
  Exception raised when [Top] is reached.
*)
exception TopReached of witness list

(*
  Creates a reversed partial tree. [mode_conj] is a conjunction of modes
  activable in the initial state. [mode_to_term] is the function mapping mode
  names to their term @0.
  Originally there are no witnesses, some initial state mode, and no modes
  explored.
*)
let mk_reved_tree mode_to_term mode_conj =
  { mode_to_term ; ws = [] ; tree = Node (Num.zero, Top, mode_conj, []) }

(*
  The tree stored in a [reved_tree].
*)
let rev_tree_of { tree } = tree

(*
  Returns the list of term the conjunction of which encodes the path of modes
  leading to the current node, including the current node.

  Result goes from current depth to 0.
*)
let term_of_path mode_to_term tree =
  let rec loop tree conj = match tree with
    | Node (k, kid, mode_conj, _) ->
      let mode_at_k = (* Building constraint for this node. *)
        mode_conj
        |> List.map (fun m -> mode_to_term m |> Term.bump_state k)
        |> Term.mk_and
      in
      mode_at_k :: conj |> loop kid (* Looping. *)
    | Top -> (* Reversing for readability. *)
      List.rev conj
  in
  loop tree

(*
  Returns the list of mode conjunctions corresponding to a partial tree.
*)
let mode_path_of tree =
  let rec loop tree prefix = match tree with
    | Node (_, kid, mode_conj, _) -> mode_conj :: prefix |> loop kid
    | Top -> List.rev prefix
  in
  loop tree []

(*
  Returns the term encoding the path of modes represented by a tree.

  Used to check which modes can be activated to extend the path being currently
  explored.
*)
let path_of { ws ; mode_to_term ; tree } =
  match tree with
  | Node _ -> term_of_path mode_to_term tree [] |> Term.mk_and
  | Top -> TopReached ws |> raise

(*
  Returns the term encoding the path of modes leading to the current node but
  blocking its mode conjunction and explored modes.

  Used when backtracking, to see if different modes can be activated at the
  current depth.
*)
let blocking_path_of { ws ; mode_to_term ; tree } =
  match tree with
  | Node (k, kid, mode_conj, explored) ->
    mode_conj :: explored
    |> List.map (fun mode_conj -> (* Negating each mode conjunction. *)
      mode_conj |> List.map mode_to_term
      |> Term.mk_and |> Term.bump_state k |> Term.mk_not
    ) |> term_of_path mode_to_term kid (* Building path. *)
    |> Term.mk_and
  | Top -> TopReached ws |> raise

(*
  Depth of the current node of a tree.
*)
let depth_of { ws ; tree } = match tree with
| Node (k, _, _, _) -> k
| Top -> TopReached ws |> raise

(*
  Pushes a node on top of the current one, activating a mode conjunction.
*)
let push ({ ws ; tree } as t) mode_conj = match tree with
| Node (k, _, _, _) ->
  t.tree <- Node(Num.succ k, tree, mode_conj, [])
| Top -> TopReached ws |> raise

(*
  Pops the current node.
*)
let pop ({ ws ; tree } as t) = match tree with
| Node (_, kid, _, _) -> t.tree <- kid
| Top -> TopReached ws |> raise

(*
  Adds a witness for the current node.

  Used when at maximal depth to store a witness.
*)
let add_witness ({ ws ; tree } as t) model =
  t.ws <- ( model, (mode_path_of tree) ) :: ws


(* 
   Local Variables:
   compile-command: "make -C .. -k"
   indent-tabs-mode: nil
   End: 
*)
