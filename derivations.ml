module type LOGIC = sig
  type formula
  type rule_name
  type state
end

(* The proof tree for a certain type of logical formulas. *)
module Make = functor (L: LOGIC) -> struct
  type derivation =
    goal * rule

  and goal =
    (* Now that we have binders, a [goal] only makes sense in a given [state]. *)
    L.state * L.formula

  and rule =
    rule_name * premises

  and rule_name = L.rule_name

  and premises =
    (* Useless constructor to avoid creating a cyclic type abbreviation. *)
    Premises of derivation list
end
