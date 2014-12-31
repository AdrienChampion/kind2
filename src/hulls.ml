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
open TermLib

module Solver = SolverMethods.Make(SMTSolver.Make(SMTLIBSolver))

exception NoIntOrRealsInSystem

(* Solver reference for clean exit. *)
let solver_ref = ref None

(* Creates a new actlit, declares it, and returns its term version. *)
let fresh_actlit solver = 
  let uf = Actlit.fresh_actlit () in
  Solver.declare_fun solver uf ;
  Actlit.term_of_actlit uf

(* Creates a new fresh var, declares it, and returns its term
   version. *)
let fresh_var solver t =
  let fresh = Var.mk_fresh_var t in
  Var.declare_vars (Solver.declare_fun solver) [ fresh ] ;
  Term.mk_var fresh

(* A hullifier is a solver, a type map, and an int map. *)
type t =
    { trans: TransSys.t ;
      solver: Solver.t ;
      (* Maps the Int/Real type with the variables of [trans] (as
         terms) having that type, and to a term wich is the [b] used
         in the resolution of [a0*x0 + ... + an*xn = 0]. *)
      type_map: (Type.t * (Term.t list * Term.t)) list ;
      (* The int map maps int variables to fresh real ones and is used
         to prune integers lines in a real space. *)
      int_map: (Term.t * Term.t) list }

(* Builds a new hullifier from a transition system. *)
let mk_hullifier trans =

  (* Creating a new solver. *)
  let solver =
    TransSys.get_logic trans
    |> Solver.new_solver ~produce_assignments:true
  in

  (* Splits variables between integer and real valued ones. *)
  let rec split_vars ints reals = function
    | var :: tail ->
       ( match Var.type_of_var var |> Type.node_of_type with
         | Type.Int ->
            split_vars (var :: ints) reals tail
         | Type.Real ->
            split_vars ints (var :: reals) tail
         | _ ->
            split_vars ints reals tail )
    | [] -> ints, reals
  in

  (* The int and real valued variables of the system. *)
  let int_vars, real_vars =
    TransSys.vars_of_bounds trans Numeral.zero Numeral.zero
    |> split_vars [] []
  in

  (* Binding between the int type and the int vars / [b]. Map
     [int_map] maps int vars to fresh real ones. All variables,
     including fresh ones, are declared. *)
  let ints, int_map =
    match int_vars with
    | [] -> [], []
    | _ ->

       Solver.trace_comment
         solver "Declaring variables of type [int]." ;
       Var.declare_vars
         (Solver.declare_fun solver) int_vars ;

       Solver.trace_comment
         solver "Declaring fresh variable of type [int]." ;
       let fresh_b = fresh_var solver Type.t_int in

       let int_var_terms =
         int_vars |> List.map Term.mk_var
       in

       (* Int binding. *)
       [ (Type.t_int, (int_var_terms, fresh_b)) ],
       (* Map from vars to fresh real vars. *)
       int_var_terms
       |> List.map
            ( fun v ->
              Solver.trace_comment
                solver
                (Printf.sprintf
                   "Real version of %s."
                   (Term.string_of_term v)) ;
              v, fresh_var solver Type.t_real )
  in

  (* Binding between the real type and the real vars / [b]. All
     variables are declared. *)
  let reals =
    match real_vars with
    | [] -> []
    | _ ->

       Solver.trace_comment
         solver "Declaring variables of type [real]." ;
       Var.declare_vars
         (Solver.declare_fun solver) real_vars ;

       Solver.trace_comment
         solver "Declaring fresh variable of type [real]." ;
       let fresh_b = fresh_var solver Type.t_real in

       [ (Type.t_real,
          (real_vars |> List.map Term.mk_var, fresh_b)) ]
  in

  match ints @ reals with
  | [] ->
     (* No ints or reals, crashing. *)
     raise NoIntOrRealsInSystem
  | type_map ->
     (* Creating hullifier. *)
     { trans ; solver ; type_map ; int_map }

(* A polyhedra border... *)
type border =
  (* ...can be a vertex, i.e. a point... *)
  | Vertex of (Term.t * Term.t) list
  (* ...or a limit, when the polyhedra is open. *)
  | Limit of Term.t

(* Pretty prints a border. *)
let pp_print_border ppf = function
  | Vertex model ->
     Format.fprintf
       ppf
       "Vertex @[<v>%a@]"
       (pp_print_list
          (fun ppf (t,v) ->
           Format.fprintf
             ppf
             "%a -> %a"
             Term.pp_print_term t
             Term.pp_print_term v)
          "@ ")
       model
  | Limit equation ->
     Format.fprintf
       ppf
       "Limit  %a"
       Term.pp_print_term
       equation


(* Structure for a polyhedron. *)
type poly =
    { (* The polyhedron itself. *)
      poly: Term.t list ;
      (* The vertices of the polyhedron. *)
      vertices: border list ;
      (* The open version of the polyhedra. All inequalities are
         turned to strict ones. *)
      strict: Term.t list }

(* The numeral corresponding to an int. *)
let num_of n = Numeral.of_int n |> Term.mk_num

(* Turns an inequality symbol into a triplet equality, strict,
   closed. *)
let others_of_equation sym =
  match Symbol.node_of_symbol sym with
  | `GT
  | `GEQ ->
     ( fun kids ->
       Term.mk_eq kids,
       Term.mk_gt kids,
       Term.mk_geq kids )
  | `LT
  | `LEQ ->
     ( fun kids ->
       Term.mk_eq kids,
       Term.mk_lt kids,
       Term.mk_leq kids )
  | _ ->
     Event.log
       L_info
       "Error in others_of_equation: @[<v>%a@]"
       Symbol.pp_print_symbol sym ;
     assert false

let find_vertex solver vars out_of inside_of eq eq' =

  Solver.push solver ;
  Term.mk_and
    [ eq ; eq' ; inside_of ; Term.mk_not out_of ]
  |> Solver.assert_term solver ;
  if Solver.check_sat solver then (
    (* Sat, getting model. *)
    let model = Solver.get_values solver vars in
    (* Popping context. *)
    Solver.pop solver ;
    (* Returning wrapped model. *)
    Some model
  ) else (
    (* Unsat, popping context. *)
    Solver.pop solver ;
    (* No model to return. *)
    None
  )

(* Looks for [eq] in [list]. If [eq] is in [list], returns [Some
   list'] where [list'] is [list] without the first occurence of
   [eq]. Otherwise returns [None]. *)
let find_rm_eq list eq =
  let rec loop pre = function
    | eq' :: tail ->
       if eq == eq' then
         Some (List.rev_append pre tail)
       else loop (eq' :: pre) tail
    | [] -> None
  in
  loop [] list

type border_context =
    { (* Border equations with no intersection discovered yet. *)
      zero: Term.t list ;
      (* Border equations with one intersection discovered. *)
      one: Term.t list ;
      (* Border equations with two intersections discovered. *)
      two: Term.t list }

let pp_print_context ppf { zero ; one ; two } =
  Format.fprintf
    ppf
    "zero @[<v>%a@]@ \
     one  @[<v>%a@]@ \
     two  @[<v>%a@]"
    (pp_print_list
       Term.pp_print_term
       "@ ")
    zero
    (pp_print_list
       Term.pp_print_term
       "@ ")
    one
    (pp_print_list
       Term.pp_print_term
       "@ ")
    two

let point_discovered eq ({ zero ; one ; two } as context) =
  match find_rm_eq zero eq with
  | Some zero' ->
     { zero = zero' ;
       one = eq :: one ;
       two }
  | None ->
     ( match find_rm_eq one eq with
       | Some one' ->
          { zero ;
            one = one' ;
            two = eq :: two }
       | None -> context )

(* Computes the vertices of a polyhedron based on the equalities of
   its facets and its closed version. *)
let get_borders solver vars equals closed =

  (* Iterates through [vertices]. *)
  let rec loop context vertices = function
    | eq :: eqs ->

       (* Finds the points of intersection between [eq] and its input
          list of equalities. *)
       let rec inner_loop context points = function
         | eq' :: tail ->

            ( match
                find_vertex
                  solver vars Term.t_false closed eq eq'
              with
              | Some model ->
                 let context' =
                   point_discovered eq context
                   |> point_discovered eq'
                 in
                 (* Looping with new point. *)
                 inner_loop context' ((Vertex model) :: points) tail
              | None ->
                 (* Looping. *)
                 inner_loop context points tail )

         | [] -> context, points
       in

       let context', vertices' = inner_loop context vertices eqs in

       (* Computing vertices for [eq] and looking. *)
       loop context' vertices' eqs

    | [] ->
       (* Event.log *)
       (*   L_info *)
       (*   "Done generating vertices.@ \ *)
       (*    Context: @[<v>%a@]" *)
       (*   pp_print_context *)
       (*   context ; *)
       List.map (fun eq -> Limit eq) context.one
       |> List.rev_append vertices
  in

  (* Computing all vertices. *)
  loop { zero = equals ; one = [] ; two = [] } [] equals

let mk_poly solver vars poly =
  let vertices, strict, loose =
    poly
    |> List.fold_left
         ( fun (eqs,sts,los) equation ->
           
           match Term.destruct equation with
             
           | Term.T.App (sym, kids) ->
              let eq,st,lo = others_of_equation sym kids in
              eq :: eqs, st :: sts, lo :: los
                                            
           | _ ->
              Event.log
                L_info
                "Error in mk_poly: @[<v>%a@]"
                Term.pp_print_term
                equation ;
              assert false )
         ([], [], [])
    |> (fun (l1,l2,l3) ->
        Term.mk_and l3
        |> get_borders solver vars l1,
        List.rev l2,
        List.rev l3)
  in

  { poly ; vertices ; strict }

let pp_print_poly fmt { poly ; vertices ; strict } =
  Format.fprintf
    fmt
    "poly:   @[<v>%a@]@ \
     border: @[<v>%a@]@ \
     strict: @[<v>%a@]"
    (pp_print_list Term.pp_print_term "@ ")
    poly
    (pp_print_list
       pp_print_border
       "@ ")
    vertices
    (pp_print_list Term.pp_print_term "@ ")
    strict

let assert_vertex solver vertex b =
  vertex
  |> List.map
       ( fun (t,v) -> Term.mk_times [t; v] )
  |> (fun list ->
      Term.mk_eq
        [ b :: list |> Term.mk_plus ;
          num_of 0 ]
      |> Solver.assert_term solver)

let is_zero t =
  if Term.is_numeral t then
    Numeral.(zero = Term.numeral_of_term t)
  else if Term.is_decimal t then
    Decimal.(zero = Term.decimal_of_term t)
  else assert false

let compute_line_vertex solver vars b v1 v2 =
  Solver.push solver ;
  Solver.trace_comment solver "Asserting vertices." ;
  assert_vertex solver v1 b ;
  assert_vertex solver v2 b ;

  if Solver.check_sat solver then
    (* Sat, getting the values. *)
    Solver.get_values solver (b :: vars)
    (* Cleaning them. *)
    |> List.fold_left
         ( fun l (t, v) ->
           if is_zero v then l
           else
             (if t == b then v
              else Term.mk_times [t ; v ])
             :: l)
         []
    (* Summing them. *)
    |> Term.mk_plus
    (* Building equation. *)
    |> (fun sum -> Term.mk_eq [ sum ; num_of 0 ])
    (* Leaving a comment in the trace. *)
    |> (fun t ->
        Solver.trace_comment
          solver
          (Printf.sprintf
             "Generated line %s."
             (Term.string_of_term t)) ;
        Solver.pop solver ;
        Some t)
  else
    (* Unsat, no new relation. *)
    None

let compute_line_mixed solver b vertex limit =
  (* Adding a parameter to the limit. *)
  let mk_limit =
    ( match
        Term.destruct limit
      with
      | Term.T.App(_, kid :: siblings) ->
         (fun b ->
          Term.mk_plus [ kid ; b ] :: siblings
          |> Term.mk_eq)
      | _ -> failwith "AAaaAAAaaaaaaaaAAAAhhhh." )
  in
           
  Solver.push solver ;
  Solver.trace_comment solver "Asserting mixed constraints." ;
  
  vertex
  |> List.map (fun (t,v) -> Term.mk_eq [t ; v])
  |> Term.mk_and
  |> Solver.assert_term solver ;

  mk_limit b
  |> Solver.assert_term solver ;

  if Solver.check_sat solver then
    (* Sat, getting the value of [b]. *)
    match
        Solver.get_values solver [b]
    with
    | [ _, value ] ->
       Solver.pop solver ;
       Some (mk_limit value)
    | _ -> failwith "AAaaAAAaaaaaaaaAAAAhhhh."
  else (
    Solver.pop solver ;
    None
  )

let compute_line solver vars b border1 border2 =
  match
    ( match border1, border2 with
      | Vertex v1, Vertex v2 ->
         compute_line_vertex solver vars b v1 v2
      | Vertex v, Limit l ->
         compute_line_mixed solver b v l
      | Limit l, Vertex v ->
         compute_line_mixed solver b v l
      | _ -> None )
  with
  | Some line as res ->
     res
  | res ->
     res

let generate_relations solver vars b poly1 poly2 =

  Solver.trace_comment solver "Starting generate_relations." ;

  let vertices, vertices' =
    poly1.vertices, poly2.vertices
  in

  let rec loop lines = function
    | b1 :: tail ->

       let rec inner_loop lines' = function
         | b2 :: tail' ->
            ( match
                compute_line solver vars b b1 b2
              with
              | Some line ->
                 Term.TermSet.add
                   (Simplify.simplify_term [] line in)
                   lines'
              | None -> lines' )
            |> (fun l -> inner_loop l tail')

         | _ :: _ -> failwith "AAaaAAAaaaaaaaaAAAAhhhh."

         | [] -> lines'
       in
       
       Solver.push solver ;

       Solver.trace_comment
         solver "Coefficients cannot all be zero." ;
       vars
       |> List.map (fun v -> Term.mk_eq [ v ; num_of 0 ])
       |> Term.mk_and
       |> Term.mk_not
       |> Solver.assert_term solver ;

       let lines' = inner_loop lines vertices' in

       Solver.pop solver ;

       loop lines' tail

    | _ :: _ -> failwith "AAaaAAAaaaaaaaaAAAAhhhh."

    | [] ->
       lines |> Term.TermSet.elements

  in

  let prune_lines lines =
    Solver.trace_comment
      solver "Pruning lines." ;
    Solver.push solver ;
    Solver.trace_comment
      solver "Asserting strict constraint." ;
    Term.mk_or
      [ Term.mk_and poly1.strict ;
        Term.mk_and poly2.strict ]
    |> Solver.assert_term solver ;

    Solver.check_sat solver |> ignore ;

    let rec loop to_keep = function
      | [] -> to_keep
      | line :: tail ->
         Solver.push solver ;
         Solver.assert_term solver line ;
         if Solver.check_sat solver
         then (
           Solver.pop solver ;
           (* Sat, line intersects strict polys. *)
           (* Discarding it. *)
           loop to_keep tail
         ) else (
           Solver.pop solver ;
           (* Unsat, line is a frontier, keeping it. *)
           loop (line :: to_keep) tail
         )
    in

    let res = loop [] lines in
    
    Solver.pop solver ;

    res
  in

  loop Term.TermSet.empty vertices

let test trans =

  let solver =
    TransSys.get_logic trans
    |> Solver.new_solver ~produce_assignments:true
  in

  let x, y, b =
    let x_temp, y_temp, b_temp =
      Var.mk_state_var_instance
        (StateVar.mk_state_var "x" ["hull"] Type.t_int)
        Numeral.zero,
      Var.mk_state_var_instance
        (StateVar.mk_state_var "y" ["hull"] Type.t_int)
        Numeral.zero,
      Var.mk_state_var_instance
        (StateVar.mk_state_var "b" ["hull"] Type.t_int)
        Numeral.zero
    in

    [ x_temp ; y_temp ; b_temp ]
    |> Var.declare_vars (Solver.declare_fun solver) ;

    Term.mk_var x_temp, Term.mk_var y_temp, Term.mk_var b_temp
  in

  let triangle_loose =
    [ Term.mk_leq [ y ; num_of 3 ] ;
      Term.mk_geq [ x ; num_of 0 ] ;
      Term.mk_geq [ y ; x ] ]
  in

  let limit_loose_1 =
    [ Term.mk_geq [ y ;
                    Term.mk_minus
                      [ num_of 2 ; x ] ] ;
      Term.mk_geq [ y ;
                    Term.mk_minus
                      [ x ; num_of 2 ] ] ;
      Term.mk_leq [ y ;
                    Term.mk_plus
                      [ x ; num_of 2 ] ] ]
  in

  let limit_loose_2 =
    [ Term.mk_leq [ y ;
                    Term.mk_minus
                      [ x ; num_of 5 ] ] ;
      Term.mk_geq [ y ; num_of 1 ] ;
      Term.mk_leq [ y ; num_of 4 ] ]
  in

  let square_loose =
    [ Term.mk_leq [ y ; num_of 3 ] ;
      Term.mk_leq [ x ; num_of 7 ] ;
      Term.mk_geq [ y ; num_of 0 ] ;
      Term.mk_geq [ x ; num_of 4 ] ]
  in

  let troose, limoose_1, limoose_2, sqoose =
    mk_poly solver [x;y] triangle_loose,
    mk_poly solver [x;y] limit_loose_1,
    mk_poly solver [x;y] limit_loose_2,
    mk_poly solver [x;y] square_loose
  in

  (* Event.log *)
  (*   L_info *)
  (*   "Troose:  @[<v>%a@]" *)
  (*   pp_print_poly troose_poly ; *)

  Event.log
    L_info
    "Limoose 1: @[<v>%a@]"
    pp_print_poly limoose_1 ;

  Event.log
    L_info
    "Limoose 2: @[<v>%a@]"
    pp_print_poly limoose_2 ;

  (* Event.log *)
  (*   L_info *)
  (*   "Sqoose:  @[<v>%a@]" *)
  (*   pp_print_poly sqoose_poly ; *)

  let relations =
    generate_relations solver [x;y] b limoose_1 limoose_2
  in

  Event.log
    L_info
    "New relations: @[<v>%a@]"
    (pp_print_list
       Term.pp_print_term
       "@ ")
    relations ;

  ()
    

(* Runs the base instance. *)
let main = test


(* Clean up before exit *)
let on_exit _ =

  (* Delete solver instance if created. *)
  (try
      match !solver_ref with
      | None -> ()
      | Some solver ->
         Solver.delete_solver solver |> ignore ;
         solver_ref := None
    with
    | e -> 
       Event.log L_error
                 "Hulls @[<v>Error deleting solver_init:@ %s@]" 
                 (Printexc.to_string e))




(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

