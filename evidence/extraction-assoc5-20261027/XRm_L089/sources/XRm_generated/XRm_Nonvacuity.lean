import XRm_ReverseSites
import XRm_DotAssociation
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRm_Nonvacuity
theorem reverse_prefix : ∃ c s, XRm_ReverseSites.Reached c s := by
  exact ⟨Array.repeat 8#usize 0#u32,_,.initial⟩

theorem empty_dot : ∃ s, XRl_DotHistory.Reached [] s ∧ s.count.val=0 := by
  exact ⟨XRl_WideBoundary.initial,.initial _ rfl,rfl⟩

theorem canonical_one : ∃ e, aspis_core.field.wide_exact.WideExact.ONE=ok e ∧
    XRm_WideProducer.Canonical e := ⟨_,rfl,XRm_WideProducer.one⟩

/-- The former arbitrary-history counterexample remains valid. Our producer
theorems restrict the actual caller domain; they do not erase this boundary. -/
theorem noncanonical_history : ∃ s,
    XRl_DotHistory.Reached [(XRl_WideBoundary.invalidWide,qzero)] s ∧
    ¬ XRl_WideCanonical.Canonical XRl_WideBoundary.invalidWide := by
  obtain ⟨s,run⟩ := XRl_WideBoundary.invalid_wide_accepted
  exact ⟨s,.push (.initial _ rfl) _ _ run,fun h => XRl_WideBoundary.invalid_coordinate h.1⟩
#print axioms reverse_prefix
#print axioms empty_dot
#print axioms canonical_one
#print axioms noncanonical_history
end XRm_Nonvacuity
