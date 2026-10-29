import Init

namespace PV_B3P_Domain16227

/-- Flatten only the field limbs of the arguments narrowed by a native gate.
The actual source-to-feed association and this proposition for the deployed
feed are OPEN. A public M31(u32) wrapper does not enforce this proposition. -/
def PV_B3P_Link_callers_canonical16 {Call : Type}
    (suppliedWords : Call → List Nat) : Prop :=
  ∀ call word, word ∈ suppliedWords call → word < 2147483647

/-- An explicit nonempty model witness. This proves joint satisfiability of
this proposed domain condition, never canonicality of actual deployed calls. -/
theorem canonical_call_domain_nonvacuous16 :
    ∃ suppliedWords : Unit → List Nat,
      PV_B3P_Link_callers_canonical16 suppliedWords ∧
      suppliedWords () = [0, 0, 0, 0] := by
  refine ⟨fun _ => [0, 0, 0, 0], ?_, rfl⟩
  intro call word member
  have positive : 0 < 2147483647 := Nat.zero_lt_succ 2147483646
  rcases List.mem_cons.mp member with first | rest
  · cases first; exact positive
  rcases List.mem_cons.mp rest with second | rest
  · cases second; exact positive
  rcases List.mem_cons.mp rest with third | rest
  · cases third; exact positive
  rcases List.mem_cons.mp rest with fourth | rest
  · cases fourth; exact positive
  exact False.elim (List.not_mem_nil word rest)

#print axioms canonical_call_domain_nonvacuous16
end PV_B3P_Domain16227
