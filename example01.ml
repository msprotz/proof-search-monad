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

and state = descr P.state

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


(** Helpers to deal with the stateironment. *)

(* The empty stateironment *)
let empty: state = P.init ()

let bind_rigid (state: state): var * state =
  P.create Rigid state

let bind_flexible (state: state): var * state =
  P.create Flexible state

(* Two variables can be unified as long as one of them is flexible, or that they
 * are two equal rigids. Two flexibles unify into the same flexible; a flexible
 * unifies with a rigid instantiates onto that rigid. *)
let unify (state: state) (v1: var) (v2: var): state option =
  match P.find v1 state, P.find v2 state with
  | Flexible, Flexible
  | Flexible, Rigid ->
      return (P.union v1 v2 state)
  | Rigid, Flexible ->
      return (P.union v2 v1 state)
  | Rigid, Rigid ->
      if P.same v1 v2 state then
        return state
      else
        nothing


(** Solving *)

let rec solve (state: state) (formula: formula): state option =
  match formula with
  | Equals (v1, v2) ->
      unify state v1 v2
  | And (f1, f2) ->
      solve state f1 >>= fun state ->
      solve state f2


let _ =
  let state = empty in
  let x, state = bind_rigid state in
  let y, state = bind_flexible state in
  let z, state = bind_rigid state in
  (* x = ?y /\ z = z *)
  let f1 = And (Equals (x, y), Equals (z, z)) in
  (* x = ?y /\ ?y = z *)
  let f2 = And (Equals (x, y), Equals (y, z)) in
  assert (solve state f1 <> None);
  assert (solve state f2 = None);
  ()
