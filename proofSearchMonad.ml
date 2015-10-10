open Lib
open Monads

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

module ProofMonad = Monads.Make(Formula)

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
let unify (env: env) (v1: var) (v2: var) =
  let open MOption in
  match P.find v1 env, P.find v2 env with
  | Flexible, Flexible
  | Flexible, Rigid ->
      return (P.union v1 v2 env)
  | Rigid, Flexible ->
      return (P.union v2 v1 env)
  | Rigid, Rigid ->
      if P.same v1 v2 env then
        return env
      else
        nothing

let try_refl (env: env) (v1: var) (v2: var) =
  let goal = Equals (v1, v2) in
  if P.same v1 v2 env then
    axiom env goal R_Refl
  else
    fail


(** Solving *)

let rec solve (env: env) (goal: formula): env outcome =
  match goal with
  | Equals (v1, v2) ->
      (* try_refl env v1 v2 ||| *)

      (* try_unify env v1 v2 >>= fun env -> *)
      (* try_refl env v1 v2 >>= *)
      (* qed *)
      assert false
  | And (f1, f2) ->
      prove goal R_And begin
        premise (solve env f1) >>= fun env ->
        premise (solve env f2) >>=
        return
      end


let _ =
  let env = empty in
  let x, env = bind_rigid env in
  let y, env = bind_flexible env in
  let z, env = bind_rigid env in
  (* x = ?y /\ z = z *)
  let f1 = And (Equals (x, y), Equals (z, z)) in
  (* x = ?y /\ ?y = z *)
  let f2 = And (Equals (x, y), Equals (y, z)) in
  assert (is_Some (solve env f1));
  assert (is_None (solve env f2));
  ()
