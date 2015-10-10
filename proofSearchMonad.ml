module P = PersistentUnionFind

module Formula = struct
  (** Formulas *)

  (* Conjunction of equalities. *)
  type formula =
    | Equals of var * var
    | And of formula * formula

  (** Variables as equivalence classes in a union-find. *)

  (* A variable is an equivalence class that resolves to either a flexible or a
   * rigid variable. The [descr] field would typically be more sophisticated. For
   * instance, we may want to use levels to make sure that only legal
   * instantiations are performed. *)
  and descr =
    | Flexible
    | Rigid

  (* Variables are defined using a persistent union-find data structure. *)
  and var = P.point

  and env = descr P.state

  (* Destructors. *)
  let assert_equals =
    function Equals (v1, v2) -> v1, v2 | _ -> assert false
  let assert_and =
    function And (f1, f2) -> f1, f2 | _ -> assert false

end

module ProofMonad = Monads.Make(Formula)(Monads.MExplore)

open ProofMonad
open Formula


(** Helpers to deal with the environment. *)

(* The empty environment *)
let empty: env = P.init ()

let bind_rigid (env: env): var * env =
  P.create Rigid env

let bind_flexible (env: env): var * env =
  P.create Flexible env


(* Two variables can be unified as long as one of them is flexible, or that they
 * are two equal rigids. Two flexibles unify into the same flexible; a flexible
 * unifies with a rigid instantiates onto that rigid. *)
let rec prove_equality (env: env) (goal: goal) (v1: var) (v2: var) =
  match P.find v1 env, P.find v2 env with
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


module Test = struct

  let is_Cons x = LazyList.(next x <> Nil)
  let is_Nil x = LazyList.(next x = Nil)

  let _ =
    let env = empty in
    let x, env = bind_rigid env in
    let y, env = bind_flexible env in
    let z, env = bind_rigid env in
    (* x = ?y /\ z = z *)
    let g1 = And (Equals (x, y), Equals (z, z)) in
    (* x = ?y /\ ?y = z *)
    let g2 = And (Equals (x, y), Equals (y, z)) in
    assert (is_Cons (solve env g1));
    assert (is_Nil (solve env g2));
    ()

end
