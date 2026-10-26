import R1Z.PV_RW_Outcome
set_option autoImplicit false
namespace R1Z.PV_RW_OutcomeProduct
open PV_RW_Outcome

theorem joint_injective {E A B : Type} (left right : Outcome E (A × B))
    (first : map id Prod.fst left=map id Prod.fst right)
    (second : map id Prod.snd left=map id Prod.snd right) : left=right := by
  cases left with
  | fail error => cases right <;> cases first <;> rfl
  | div => cases right <;> cases first <;> rfl
  | ok pair =>
    cases right with
    | fail error => cases first
    | div => cases first
    | ok other =>
      have ha : pair.1=other.1 := Outcome.ok.inj first
      have hb : pair.2=other.2 := Outcome.ok.inj second
      exact congrArg Outcome.ok (Prod.ext ha hb)

theorem equal_iff {E A B : Type} (left right : Outcome E (A × B)) :
    left=right ↔ (map id Prod.fst left=map id Prod.fst right ∧
      map id Prod.snd left=map id Prod.snd right) := by
  constructor
  · intro same
    exact ⟨congrArg (map id Prod.fst) same,congrArg (map id Prod.snd) same⟩
  · rintro ⟨first,second⟩
    exact joint_injective left right first second
#print axioms joint_injective
#print axioms equal_iff
end R1Z.PV_RW_OutcomeProduct
