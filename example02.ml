(* Second example: this is the version at the end of §3, which builds
 * derivations automatically _and_ backtracks. *)

module P = PersistentUnionFind

module Formula = struct
  (** Formulas *)

  (* Conjunctions and disjunction of equalities between variables. *)
  type formula =
    | Equals of var * var
    | And of formula * formula
    | Or of formula * formula

  (** Variables as equivalence classes in a union-find. *)

  (* A variable is an equivalence class that resolves to either a flexible or a
   * rigid variable. The [descr] field would typically be more sophisticated. For
   * instance, we may want to use levels to make sure that only legal
   * instantiations are performed. *)
  and descr = status * string

  and status =
    | Flexible
    | Rigid

  (* Variables are defined using a persistent union-find data structure. *)
  and var = P.point

  and state = descr P.state

  type rule_name =
    | R_And
    | R_Instantiate
    | R_Refl
    | R_OrL
    | R_OrR
end

(* [MExplore] and [MOption] both work here; only [MExplore] implements
 * backtracking. Switch to [MOption] to get the implementation at the end of §2
 * in the paper. *)
module M = Combinators2.MExplore
module ProofMonad = Combinators2.Make(Formula)(M)

open ProofMonad
open Formula


(** Helpers to deal with the stateironment. *)

(* The empty stateironment *)
let empty: state = P.init ()

let bind_rigid (state: state) (name: string): var * state =
  P.create (Rigid, name) state

let bind_flexible (state: state) (name: string): var * state =
  P.create (Flexible, name) state

let find v state = fst (P.find v state)

let name v state =
  match P.find v state with
  | Rigid, name ->
      name
  | Flexible, name ->
      "?" ^ name


(* Two variables can be unified as long as one of them is flexible, or that they
 * are two equal rigids. Two flexibles unify into the same flexible; a flexible
 * unifies with a rigid and instantiates onto that rigid. *)
let rec prove_equality (state: state) (goal: goal) (v1: var) (v2: var) =
  match find v1 state, find v2 state with
  | Flexible, Flexible
  | Flexible, Rigid ->
      let state = P.union v1 v2 state in
      prove goal begin
        premise (prove_equality state goal v1 v2) >>=
        qed R_Instantiate
      end
  | Rigid, Flexible ->
      let state = P.union v2 v1 state in
      prove goal begin
        premise (prove_equality state goal v2 v1) >>=
        qed R_Instantiate
      end
  | Rigid, Rigid ->
      if P.same v1 v2 state then
        axiom state goal R_Refl
      else
        fail


(** Solving *)

let rec solve (state: state) (goal: formula): state outcome =
  match goal with
  | Equals (v1, v2) ->
      prove_equality state goal v1 v2
  | And (g1, g2) ->
      prove goal begin
        premise (solve state g1) >>= fun state ->
        premise (solve state g2) >>=
        qed R_And
      end
  | Or (g1, g2) ->
      choice goal [ R_OrL, g1; R_OrR, g2 ] (fun (side, g) ->
        premise (solve state g) >>=
        qed side
      )


(* Using the library: a pretty-printer of proof trees, along with a few test
 * helpers (to make sure our library actually does what we want). Feel free to
 * sprinkle a few [print_endline] in the solver above to make sure that nothing
 * is evaluated too much. *)
module Test = struct

  let print_derivation (state: state) (d: derivation): string =
    let p_rule = function
      | R_And -> "/\\"
      | R_Instantiate -> "inst"
      | R_Refl -> "refl"
      | R_OrL -> "\\/_l"
      | R_OrR -> "\\/_r"
    in
    let rec p_or = function
      | Or (f1, f2) ->
          p_or f1 ^ " \\/ " ^ p_or f2
      | f ->
          p_and f
    and p_and = function
      | And (f1, f2) ->
          p_and f1 ^ " /\\ " ^ p_and f2
      | Equals (v1, v2) ->
          name v1 state ^ " = " ^ name v2 state
      | f ->
          "(" ^ p_formula f ^ ")"
    and p_formula f =
      p_or f
    in
    let rec p (indent: string) (d: derivation) =
      let goal, (rule_name, Premises premises) = d in
      indent ^ "prove " ^ p_formula goal ^
        if List.length premises > 0 then
          " using [" ^ p_rule rule_name ^
          "]\n" ^
            String.concat "\n" (List.map (p (indent ^ "| ")) premises)
        else
          " using axiom [" ^ p_rule rule_name ^ "]"
    in
    p "" d


  let check b state d =
    match M.extract d with
    | Some (_state, d) ->
        assert b;
        print_endline (print_derivation state d);
        print_newline ()
    | None ->
        assert (not b);
        print_endline "fail"


  let _ =
    let state = empty in
    let x, state = bind_rigid state "x" in
    let y, state = bind_flexible state "y" in
    let z, state = bind_rigid state "z" in
    (* Example 1: « x = ?y /\ z = z ». Uses all three rules. *)
    let g1 = And (Equals (x, y), Equals (z, z)) in
    (* Example 2: « x = z /\ ?y = z ». The whole point is that the second
     * premise of the conjunction is not even evaluated (since the first one
     * failed). *)
    let g2 = And (Equals (x, z), Equals (y, z)) in
    (* Example 3: « (x = z \/ z = z) ». This one requires search but no
     * backtracking, meaning it will fail with [MOption] but succeed with
     * [MExplore]. *)
    let g3 = Or (Equals (x, z), Equals (z, z)) in
    (* Example 4: « (?y = x \/ ?y = z) /\ ?y = z ». This one backtracks. *)
    let g4 = And (Or (Equals (y, x), Equals (y, z)), Equals (y, z)) in
    (* Example 5: « (x = z \/ (?y = x /\ ?y = z)) ». This one fails, but the
     * explanation is non-trivial. *)
    let g5 = Or (Equals (x, z), And (Equals (y, x), Equals (y, z))) in
    check true state (solve state g1);
    check false state(solve state g2);
    check true state (solve state g3);
    check true state (solve state g4);
    check false state (solve state g5);
    ()

end
