open ProofTree

module type MONAD = sig
  type 'a m
  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m
  val ( >>= ): 'a m -> ('a -> 'b m) -> 'b m

  val nothing: 'a m
  val extract: 'a m -> 'a option
  val search: ('a -> 'b m) -> 'a list -> 'b m
end

module MOption: MONAD with type 'a m = 'a option = struct
  type 'a m = 'a option
  let return x = Some x
  let bind x f =
    match x with
    | Some x -> f x
    | None -> None
  let ( >>= ) = bind
  let nothing = None
  let extract x = x
  let rec search f l =
    match l with
    | [] -> None
    | x :: xs ->
        match f x with
        | Some x -> Some x
        | None -> search f xs
end

module MExplore: MONAD with type 'a m = 'a LazyList.t = struct
  open LazyList
  type 'a m = 'a t
  let return = one
  let bind x f = flattenl (map f x)
  let ( >>= ) = bind
  let nothing = nil
  let extract x =
    match next x with
    | Nil -> None
    | Cons (x, _) -> Some x
  let search f l =
    bind (of_list l) f
end

module type MONOID = sig
  type a
  val empty: a
  val append: a -> a -> a
end

module WriterT (M: MONAD) (L: MONOID): sig
  type 'a m = (L.a * 'a) M.m

  val return: 'a -> 'a m

  val tell: L.a -> unit m

  val bind: 'a m -> ('a -> 'b m) -> 'b m

  val ( >>= ): 'a m -> ('a -> 'b m) -> 'b m
end = struct
  type 'a m = (L.a * 'a) M.m

  let return x = M.return (L.empty, x)

  let tell log = M.return (log, ())

  let bind x f =
    M.bind x (fun (log, x) ->
      M.bind (f x) (fun (log', y) ->
        M.return (L.append log log', y)))

  let ( >>= ) = bind
end

module Make(Logic: LOGIC)(M: MONAD) = struct
  module Proofs = ProofTree.Make(Logic)

  (* The monoid of derivation lists. *)
  module L: MONOID with type a = Proofs.derivation list = struct
    type a = Proofs.derivation list
    let empty = []
    let append = List.append
  end

  include WriterT(M)(L)
  include Proofs

  (* The result of a proof search. *)
  type 'a outcome =
    ('a * derivation) M.m

  (* Injection of an ['a outcome] into the monad (it becomes a premise). *)
  let premise (outcome: 'a outcome): 'a m =
    M.bind outcome (fun (env, derivation) ->
      tell [ derivation ] >>= fun () ->
      return env
    )

  (* Equivalent of [runMProof]: collect the premises in order to compute the
   * outcome. *)
  let prove (goal: goal) (x: ('a * rule_name) m): 'a outcome =
    M.(x >>= fun (premises, (env, rule)) ->
      return (env, (goal, (rule, Premises premises))))

  (* Create an outcome from an axiom. *)
  let axiom (env: 'a) (goal: goal) (axiom: rule_name): 'a outcome =
    prove goal (return (env, axiom))

  (* The failed outcome. *)
  let fail: 'a outcome =
    M.nothing

  (* Multiple choices -- may or may not backtrack, depending on [M]. *)
  let choice (goal: goal) (args: 'a list) (f: 'a -> ('b * rule_name) m): 'b outcome =
    M.search (fun x -> prove goal (f x)) args
end
