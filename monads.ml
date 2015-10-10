open ProofTree

module type MONAD = sig
  type 'a m
  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m
  val ( >>= ): 'a m -> ('a -> 'b m) -> 'b m

  val nothing: 'a m
  val of_list: 'a m list -> 'a m
end

module type MONOID = sig
  type a
  val empty: a
  val append: a -> a -> a
end

module MOption: sig
  type 'a m = 'a option
  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m
  val ( >>= ): 'a m -> ('a -> 'b m) -> 'b m
  val nothing: 'a m
  val of_list: 'a m list -> 'a m
end = struct
  type 'a m = 'a option
  let return x = Some x
  let bind x f =
    match x with
    | Some x -> f x
    | None -> None
  let ( >>= ) = bind
  let nothing = None
  let rec of_list = function
    | Some x :: _ -> Some x
    | None :: xs -> of_list xs
    | [] -> None
end

module MExplore: sig
  type 'a m = 'a LazyList.t
  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m
  val ( >>= ): 'a m -> ('a -> 'b m) -> 'b m
  val nothing: 'a m
  val of_list: 'a m list -> 'a m
end = struct
  type 'a m = 'a LazyList.t
  let return = LazyList.one
  let bind x f =
    LazyList.flattenl (LazyList.map f x)
  let ( >>= ) = bind
  let nothing = LazyList.nil
  let of_list = LazyList.flatten
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

module Make(F: FORMULA)(M: MONAD) = struct
  module Proofs = ProofTree.Make(F)

  (* The monoid of derivation lists. *)
  module L = struct
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
  let prove (goal: goal) (rule: rule_name) (x: 'a m): 'a outcome =
    M.(x >>= fun (premises, env) ->
      return (env, (goal, (rule, Premises (List.rev premises)))))

  (* Create an outcome from an axiom. *)
  let axiom (env: 'a) (goal: goal) (axiom: rule_name): 'a outcome =
    prove goal axiom (return env)

  (* The failed outcome. *)
  let fail: 'a outcome =
    M.nothing

  let choice (goal: goal) (args: (rule_name * 'a) list) (f: 'a -> 'b m): 'b outcome =
    M.of_list (List.map (fun (r, x) -> prove goal r (f x)) args)
end
