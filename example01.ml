(* First example: just the option monad. *)

module P = PersistentUnionFind

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

(** The option monad. *)

module Option = struct
  let return = fun x -> Some x
  let ( >>= ) x f =
    match x with
    | Some x -> f x
    | None -> None
  let nothing = None
end

open Option


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
let unify (env: env) (v1: var) (v2: var): env option =
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


(** Solving *)

let rec solve (env: env) (formula: formula): env option =
  match formula with
  | Equals (v1, v2) ->
      unify env v1 v2
  | And (f1, f2) ->
      solve env f1 >>= fun env ->
      solve env f2


let _ =
  let env = empty in
  let x, env = bind_rigid env in
  let y, env = bind_flexible env in
  let z, env = bind_rigid env in
  (* x = ?y /\ z = z *)
  let f1 = And (Equals (x, y), Equals (z, z)) in
  (* x = ?y /\ ?y = z *)
  let f2 = And (Equals (x, y), Equals (y, z)) in
  assert (solve env f1 <> None);
  assert (solve env f2 = None);
  ()
