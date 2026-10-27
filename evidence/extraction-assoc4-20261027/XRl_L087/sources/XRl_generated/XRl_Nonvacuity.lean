import XRl_DotHistory
import XRl_WideCanonical
import XRl_QueryGeometry
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
namespace XRl_Nonvacuity
/-- Actual modeled new, rather than an assumed caller state. -/
theorem empty_history :
    ∃ s, XRl_DotHistory.Reached [] s ∧ s.count.val=0 := by
  exact ⟨XRl_WideBoundary.initial,.initial _ rfl,rfl⟩

/-- The extracted history predicate itself admits a noncanonical WideExact
operand. This is a counterexample to deriving native private invariants from
arbitrary extracted histories, not a native Rust counterexample. -/
theorem bad_wide_history :
    ∃ s, XRl_DotHistory.Reached [(XRl_WideBoundary.invalidWide,qzero)] s ∧
      ¬ XRl_WideCanonical.Canonical XRl_WideBoundary.invalidWide := by
  obtain ⟨s,run⟩ := XRl_WideBoundary.invalid_wide_accepted
  refine ⟨s,?_,fun h => XRl_WideBoundary.invalid_coordinate h.1⟩
  exact .push (.initial XRl_WideBoundary.initial rfl) _ _ run

theorem validated_wide_domain :
    ∃ e, aspis_core.field.wide_exact.WideExact.from_limbs (Array.repeat 8#usize 0#u32)=ok (some e) ∧
      XRl_WideCanonical.Canonical e := by
  let e : XRk_Wide := ⟨oldQ qzero,oldQ qzero⟩
  have run : aspis_core.field.wide_exact.WideExact.from_limbs (Array.repeat 8#usize 0#u32)=ok (some e) := by rfl
  exact ⟨e,run,XRl_WideCanonical.from_limbs _ e run⟩
#print axioms empty_history
#print axioms bad_wide_history
#print axioms validated_wide_domain
end XRl_Nonvacuity
