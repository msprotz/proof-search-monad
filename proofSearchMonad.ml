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

  and env = descr P.state
end

(* [MExplore] and [MOption] both work here. *)
module M = Monads.MExplore
module ProofMonad = Monads.Make(Formula)(M)

open ProofMonad
open Formula


(** Helpers to deal with the environment. *)

(* The empty environment *)
let empty: env = P.init ()

let bind_rigid (env: env) (name: string): var * env =
  P.create (Rigid, name) env

let bind_flexible (env: env) (name: string): var * env =
  P.create (Flexible, name) env

let find v env = fst (P.find v env)

let name v env =
  match P.find v env with
  | Rigid, name ->
      name
  | Flexible, name ->
      "?" ^ name


(* Two variables can be unified as long as one of them is flexible, or that they
 * are two equal rigids. Two flexibles unify into the same flexible; a flexible
 * unifies with a rigid and instantiates onto that rigid. *)
let rec prove_equality (env: env) (goal: goal) (v1: var) (v2: var) =
  match find v1 env, find v2 env with
  | Flexible, Flexible
  | Flexible, Rigid ->
      let env = P.union v1 v2 env in
      prove goal R_Instantiate begin
        premise (prove_equality env goal v1 v2) >>=
        return
      end
  | Rigid, Flexible ->
      let env = P.union v2 v1 env in
      prove goal R_Instantiate begin
        premise (prove_equality env goal v2 v1) >>=
        return
      end
  | Rigid, Rigid ->
      if P.same v1 v2 env then
        axiom env goal R_Refl
      else
        fail


(** Solving *)

let rec solve (env: env) (goal: formula): env outcome =
  match goal with
  | Equals (v1, v2) ->
      prove_equality env goal v1 v2
  | And (g1, g2) ->
      prove goal R_And begin
        premise (solve env g1) >>= fun env ->
        premise (solve env g2) >>=
        return
      end
  | Or (g1, g2) ->
      choice goal [ R_OrL, g1; R_OrR, g2 ] (fun g ->
        premise (solve env g) >>=
        return
      )


module Test = struct

  let print_derivation (env: env) (d: derivation): string =
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
          name v1 env ^ " = " ^ name v2 env
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


  let check b env d =
    match M.extract d with
    | Some (_env, d) ->
        assert b;
        print_endline (print_derivation env d);
        print_newline ()
    | None ->
        assert (not b);
        print_endline "fail"


  let _ =
    let env = empty in
    let x, env = bind_rigid env "x" in
    let y, env = bind_flexible env "y" in
    let z, env = bind_rigid env "z" in
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
    check true env (solve env g1);
    check false env(solve env g2);
    check true env (solve env g3);
    check true env (solve env g4);
    check false env (solve env g5);
    ()

end
