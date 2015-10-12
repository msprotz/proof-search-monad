(* Third version: produces a derivation that more closely matches the rules from
 * the logic, rather than the algorithmic rules. *)
module P = PersistentUnionFind

module Formula = struct
  (** Formulas *)

  (* Conjunctions and disjunction of equalities between variables. *)
  type formula =
    | Equals of var * var
    | And of formula * formula
    | Or of formula * formula
    | Exists of atom * formula
    | Forall of atom * formula

  (** Variables as equivalence classes in a union-find. *)

  (* A variable is an equivalence class that resolves to either a flexible or a
   * rigid variable. The [descr] field would typically be more sophisticated. For
   * instance, we may want to use levels to make sure that only legal
   * instantiations are performed. *)
  and descr = status * atom

  and atom = string

  and status =
    | Flexible
    | Rigid

  (* This is a full example with binders... for simplicity purposes, closed
   * variables are identified using atoms (string); open variables have an
   * existence in the union-find. *)
  and var =
    | Open of P.point
    | Closed of atom

  and state = descr P.state

  type rule_name =
    | R_And
    | R_Refl of atom
    | R_OrL
    | R_OrR
    | R_Exists of atom
    | R_Forall

  let assert_open = function
    | Open v -> v
    | Closed _ -> failwith "assert_open"
end

(* [MExplore] and [MOption] both work here; only [MExplore] implements
 * backtracking. *)
module M = Combinators.MExplore
module ProofMonad = Combinators.Make(Formula)(M)

open ProofMonad
open Formula


(** Helpers to deal with the stateironment. *)

(* The empty stateironment *)
let empty: state = P.init ()

let bind_rigid (state: state) (name: string): var * state =
  let point, state = P.create (Rigid, name) state in
  Open point, state

let bind_flexible (state: state) (name: atom): var * state =
  let point, state = P.create (Flexible, name) state in
  Open point, state

(* Replace [x] with [y] in [f]. *)
let subst_var (x: var) (y: var) (f: var): var =
  match x, y with
  | Closed _, Open _ ->
      ()
  | _ ->
      failwith "subst_var"; ;
  match x, f with
  | Closed atom, Closed atom' when atom = atom' ->
      y
  | _ ->
      f

(* Replace [x] with [y] in [f']. *)
let rec subst (x: var) (y: var) (f: formula): formula =
  match f with
  | And (f1, f2) ->
      And (subst x y f1, subst x y f2)
  | Or (f1, f2) ->
      Or (subst x y f1, subst x y f2)
  | Exists (binder, f') ->
      Exists (binder, subst x y f')
  | Forall (binder, f') ->
      Forall (binder, subst x y f')
  | Equals (v1, v2) ->
      Equals (subst_var x y v1, subst_var x y v2)

let open_flexible (state: state) (x: atom) (f: formula): var * formula * state =
  let var, state = bind_flexible state x in
  var, subst (Closed x) var f, state

let open_rigid (state: state) (x: atom) (f: formula): var * formula * state =
  let var, state = bind_rigid state x in
  var, subst (Closed x) var f, state

let find v state =
  fst (P.find v state)

let name v state =
  match P.find v state with
  | Rigid, name ->
      name
  | Flexible, name ->
      "?" ^ name


(* Two variables can be unified as long as one of them is flexible, or that they
 * are two equal rigids. Two flexibles unify into the same flexible; a flexible
 * unifies with a rigid and instantiates onto that rigid. *)
let rec prove_equality (state: state) (goal: formula) (v1: var) (v2: var) =
  let v1 = assert_open v1 in
  let v2 = assert_open v2 in
  let rule state = R_Refl (name v1 state) in
  match find v1 state, find v2 state with
  | Flexible, Flexible
  | Flexible, Rigid ->
      let state = P.union v1 v2 state in
      axiom state goal (rule state)
  | Rigid, Flexible ->
      let state = P.union v2 v1 state in
      axiom state goal (rule state)
  | Rigid, Rigid ->
      if P.same v1 v2 state then
        axiom state goal (rule state)
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
  | Exists (atom, g) ->
      let var, g, state = open_flexible state atom g in
      let var = assert_open var in
      prove goal begin
        premise (solve state g) >>= fun state ->
        qed (R_Exists (name var state)) state
      end
  | Forall (atom, g) ->
      let var, g, state = open_rigid state atom g in
      prove goal begin
        premise (solve state g) >>=
        qed R_Forall
      end


(* A module with a pretty-printer. *)
module Test = struct

  let print_derivation (d: derivation): string =
    let p_rule = function
      | R_And -> "/\\"
      | R_OrL -> "\\/_l"
      | R_OrR -> "\\/_r"
      | R_Exists atom -> "exists["^atom^"]"
      | R_Forall -> "forall"
      | R_Refl atom -> "refl["^atom^"]"
    in
    (* Hack alert. Not opening the variables for printing because their
     * name is also the atom we use to identify them... *)
    let p_var state = function
      | Closed name -> name
      | Open p -> name p state
    in
    let rec p_quantified state = function
      | Forall (atom, f) ->
          "∀" ^ atom ^ ". " ^ p_quantified state f
      | Exists (atom, f) ->
          "∃" ^ atom ^ ". " ^ p_quantified state f
      | f ->
          p_or state f
    and p_or state = function
      | Or (f1, f2) ->
          p_or state f1 ^ " \\/ " ^ p_or state f2
      | f ->
          p_and state f
    and p_and state = function
      | And (f1, f2) ->
          p_and state f1 ^ " /\\ " ^ p_and state f2
      | Equals (v1, v2) ->
          p_var state v1 ^ " = " ^ p_var state v2
      | f ->
          "(" ^ p_formula state f ^ ")"
    and p_formula state f =
      p_quantified state f
    in
    let rec p (indent: string) (d: derivation) =
      let (state, formula), (rule_name, Premises premises) = d in
      indent ^ "prove " ^ p_formula state formula ^
        if List.length premises > 0 then
          " using [" ^ p_rule rule_name ^
          "]\n" ^
            String.concat "\n" (List.map (p (indent ^ "| ")) premises)
        else
          " using axiom [" ^ p_rule rule_name ^ "]"
    in
    p "" d


  let check b d =
    match M.extract d with
    | Some (_state, d) ->
        assert b;
        print_endline (print_derivation d);
        print_newline ()
    | None ->
        assert (not b);
        print_endline "fail"


  let _ =
    let state = empty in
    (* This test file does not check that the formulas are well-formed (i.e.
     * that all the variables are bound. *)
    let x = Closed "x" in
    let y = Closed "y" in
    let z = Closed "z" in
    let t1 = Closed "t1" in
    let t2 = Closed "t2" in
    (* Wrap with all proper quantifiers (the same in all our examples) *)
    let quantify f = Forall ("x", Forall ("z", Exists ("y", f))) in
    let quantify' f = Exists ("t1", Exists ("t2", f)) in
    (* Example 1: « x = ?y /\ z = z ». Uses all three rules. *)
    let g1 = quantify (And (Equals (x, y), Equals (z, z))) in
    (* Example 2: « x = z /\ ?y = z ». The whole point is that the second
     * premise of the conjunction is not even evaluated (since the first one
     * failed). *)
    let g2 = quantify (And (Equals (x, z), Equals (y, z))) in
    (* Example 3: « (x = z \/ z = z) ». This one requires search but no
     * backtracking, meaning it will fail with [MOption] but succeed with
     * [MExplore]. *)
    let g3 = quantify (Or (Equals (x, z), Equals (z, z))) in
    (* Example 4: « (?y = x \/ ?y = z) /\ ?y = z ». This one backtracks. *)
    let g4 = quantify (And (Or (Equals (y, x), Equals (y, z)), Equals (y, z))) in
    (* Example 5: « (x = z \/ (?y = x /\ ?y = z)) ». This one fails, but the
     * explanation is non-trivial. *)
    let g5 = quantify (Or (Equals (x, z), And (Equals (y, x), Equals (y, z)))) in
    (* Example 6: with nested quantifiers: (x = ?y /\ (∃t1, t2. (t1 = t2) \/ ∃t1, t2. (t1 = x /\ t2 = z)  *)
    let g6 = quantify (And (Equals (x, y), And (
      quantify' (Equals (t1, t2)),
      quantify' (And (Equals (t1, x), Equals (t2, z)))))) in
    check true (solve state g1);
    check false (solve state g2);
    check true (solve state g3);
    check true (solve state g4);
    check false (solve state g5);
    check true (solve state g6);
    ()

end
