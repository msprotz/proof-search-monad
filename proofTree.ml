module type FORMULA = sig
  type formula
end

(* The proof tree for a certain type of logical formulas. *)
module Make = functor (F: FORMULA) -> struct
  type derivation =
    goal * rule

  and goal =
    F.formula

  and rule =
    rule_name * premises

  and rule_name =
    | R_And
    | R_Instantiate
    | R_Refl

  and premises =
    (* Useless constructor to avoid creating a cyclic type abbreviation. *)
    Premises of derivation list
end
