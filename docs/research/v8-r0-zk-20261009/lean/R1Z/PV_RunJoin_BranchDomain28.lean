import R1Z.PV_RunJoin_ControlDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BranchDomain28
theorem ite_iff (p : Prop) [Decidable p] (a b c d : Prop)
    (ht : p → (a ↔ c)) (hf : ¬p → (b ↔ d)) :
    (if p then a else b) ↔ (if p then c else d) := by
  by_cases h : p
  · simpa only [if_pos h] using ht h
  · simpa only [if_neg h] using hf h
#print axioms ite_iff
end R1Z.PV_RunJoin_BranchDomain28
