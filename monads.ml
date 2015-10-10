open ProofTree

module type MONAD = sig
  type 'a m
  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m
end

module type MONOID = sig
  type a
  val empty: a
  val append: a -> a -> a
end

(* A monad. *)
module MOption: sig
  type 'a m = 'a option
  val return: 'a -> 'a m
  val bind: 'a m -> ('a -> 'b m) -> 'b m
  val ( >>= ): 'a m -> ('a -> 'b m) -> 'b m
  val nothing: 'a m
end = struct
  type 'a m = 'a option
  let return x = Some x
  let bind x f =
    match x with
    | Some x -> f x
    | None -> None
  let ( >>= ) = bind
  let nothing = None
end

(* A monad transformer -- signature for monad transformers not written yet. *)
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

(* The monoid of derivation lists. *)
module DList (F: FORMULA) = struct
  type a = Make(F).derivation list
  let empty = []
  let append = List.append
end

(* The monad of proofs. *)
module MProof(F: FORMULA) = WriterT(MOption)(DList(F))

(* Now with outcomes + derivations. *)
module Make(F: FORMULA) = struct
  include MProof(F)
  include Make(F)

  (* Injection of an ['a outcome] into the monad (it becomes a premise). *)
  let premise (outcome: 'a outcome): 'a m =
    MOption.bind outcome (fun (env, derivation) ->
      tell [ derivation ] >>= fun () ->
      return env
    )

  (* Equivalent of [runMProof]: collect the premises in order to compute the
   * outcome. *)
  let prove (goal: goal) (rule: rule_name) (x: 'a m): 'a outcome =
    MOption.(x >>= (fun (premises, env) ->
      return (env, (goal, (rule, Premises (List.rev premises))))))

  (* Create an outcome from an axiom. *)
  let axiom (env: 'a) (goal: goal) (axiom: rule_name): 'a outcome =
    prove goal axiom (return env)

  (* The failed outcome. *)
  let fail: 'a outcome =
    None
end
