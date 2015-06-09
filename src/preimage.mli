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

(** Internaly the context maintains a solver with the transition relation
    at [(0,1)]. Three actlits are used, and changed by [inc].

    * [src_actlit]:
      activates the terms we are computing the preimage of, at [1].
    * [blk_actlit]:
      activates the negation of the disjuncts of the preimage we have computed
      this far, _for this iteration_, at [0].
    * [nxt_actlit]:
      activates the disjuncts of the preimage we have computed this far, _for
      this iteration_, at [1].

    Function [inc] increments the context so that [get_disjunct] computes the
    preimage of the one it was computing before the call to [inc]. The optional
    argument [blocking] to [mk_context] will force preimage computation to look
    for models outside of the previously computed preimages. *)

(** Stores info needed to compute preimages. *)
type context

(** The system stored in a context. *)
val get_sys : context -> TransSys.t

(** The number of times a system has been incremented. *)
val get_k : context -> int

(** Creates a new context from a transition system and a term to compute the
    preimages of.

    Optional argument [blocking]: if true then points / disjuncts from previous
    iterations will be blocked, i.e. cannot be returned by [get_disjunct].

    /!\ The term is assumed to only mention variables at [0]. /!\ *)
val mk_context : ?blocking:bool -> TransSys.t -> Term.t -> context

(** Computes a new disjunct of the preimage. *)
val get_disjunct : context -> Term.t list option

(** Exception thrown when incrementing a context with an empty [nxt]. *)
exception NoPreimage of int

(** Increments the context: next call to [get_disjunct] will compute the
    preimage of the preimage that was being computed before the call to
    [inc].

    Raises [NoPreimage k] if there is no more preimage to compute at [k]. *)
val inc : context -> unit

(** Destroys a context, i.e. destroys the internal solver instance. *)
val destroy : context -> unit

(** Test function. *)
val test : TransSys.t -> unit

(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)
