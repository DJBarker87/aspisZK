import FinishDotConcreteOps
import CurrentFinishField
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotConcreteOps
open AspisR1CurrentWide.Proof AspisR1FinishDotSourceABI AspisR1FinishRelationCurrent

def withConcreteDotField {W : Type} (base : FinishOps W PushState)
    (rawFn : AspisR1EbyKPushDotBackend.RawFn) : FinishOps W PushState :=
  withConcreteDot (finishConcreteField base) rawFn

theorem canonical_value_raw_inputs (v : FinishE) (hv : CanonicalFinish v) :
    (∀ x ∈ (AspisR1EbyKPushDotBackend.valueLo (toPushWide v)).val, x.val<2147483647) ∧
    (∀ x ∈ (AspisR1EbyKPushDotBackend.valueHi (toPushWide v)).val, x.val<2147483647) := by
  rcases hv with ⟨⟨⟨h0,h1⟩,⟨h2,h3⟩⟩,⟨⟨h4,h5⟩,⟨h6,h7⟩⟩⟩
  constructor
  · intro x hx
    change x ∈ [v.c0.c0.a,v.c0.c0.b,v.c0.c1.a,v.c0.c1.b] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro x hx
    change x ∈ [v.c1.c0.a,v.c1.c0.b,v.c1.c1.a,v.c1.c1.b] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact h4
    · exact h5
    · exact h6
    · exact h7

theorem actual_dot_read_supplies_raw_inputs {W : Type}
    (base : FinishOps W PushState) (rawFn : AspisR1EbyKPushDotBackend.RawFn)
    (fm : Slice U8) (j : Usize) (v : FinishE)
    (hrun : (withConcreteDotField base rawFn).field fm j = .ok v) :
    (∀ x ∈ (AspisR1EbyKPushDotBackend.valueLo (toPushWide v)).val, x.val<2147483647) ∧
    (∀ x ∈ (AspisR1EbyKPushDotBackend.valueHi (toPushWide v)).val, x.val<2147483647) := by
  exact canonical_value_raw_inputs v (finishField_success_canonical fm j v hrun)

#print axioms canonical_value_raw_inputs
#print axioms actual_dot_read_supplies_raw_inputs
end AspisR1FinishDotConcreteOps
