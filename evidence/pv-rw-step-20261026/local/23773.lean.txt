import R1Z.PV_RW_OutcomeProduct
set_option autoImplicit false
namespace R1Z.PV_RW_OutcomeSumProduct
open PV_RW_Outcome

def first {V A B : Type} : Sum V (A × B) → Sum V A
  | .inl error => .inl error
  | .inr pair => .inr pair.1

def second {V A B : Type} : Sum V (A × B) → Sum V B
  | .inl error => .inl error
  | .inr pair => .inr pair.2

theorem payload_injective {V A B : Type} (left right : Sum V (A × B))
    (ha : first left=first right) (hb : second left=second right) : left=right := by
  cases left with
  | inl error => cases right <;> cases ha <;> rfl
  | inr pair =>
    cases right with
    | inl error => cases ha
    | inr other =>
      have a : pair.1=other.1 := Sum.inr.inj ha
      have b : pair.2=other.2 := Sum.inr.inj hb
      exact congrArg Sum.inr (Prod.ext a b)

theorem joint_injective {E V A B : Type} (left right : Outcome E (Sum V (A × B)))
    (ha : map id first left=map id first right)
    (hb : map id second left=map id second right) : left=right := by
  cases left with
  | fail error => cases right <;> cases ha <;> rfl
  | div => cases right <;> cases ha <;> rfl
  | ok pair =>
    cases right with
    | fail error => cases ha
    | div => cases ha
    | ok other =>
      exact congrArg Outcome.ok (payload_injective pair other (Outcome.ok.inj ha) (Outcome.ok.inj hb))

theorem equal_iff {E V A B : Type} (left right : Outcome E (Sum V (A × B))) :
    left=right ↔ (map id first left=map id first right ∧
      map id second left=map id second right) := by
  constructor
  · intro same
    exact ⟨congrArg (map id first) same,congrArg (map id second) same⟩
  · rintro ⟨ha,hb⟩
    exact joint_injective left right ha hb
#print axioms payload_injective
#print axioms joint_injective
#print axioms equal_iff
end R1Z.PV_RW_OutcomeSumProduct
