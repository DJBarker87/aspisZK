import NGC_PreparationBoundary
import NHL_PreparedRecompose
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_CanonicalPorts
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NFN_LPi_FieldValues CheckpointBytes3Namespaces OraclePortCkptAbi4Decode

theorem wide (x : aspis_core.field.WideExact)
 (h : canonE (NFW_SampledDomains.toNative x)) :
 CanonicalWide (toE (NFW_PreparedPort.e x)) :=
 ⟨⟨h.1.1.1,h.1.1.2,h.1.2.1,h.1.2.2⟩,
   ⟨h.2.1.1,h.2.1.2,h.2.2.1,h.2.2.2⟩⟩

theorem qm (x : aspis_core.field.QM31)
 (h : x.c0.a.val<2147483647 ∧ x.c0.b.val<2147483647 ∧
      x.c1.a.val<2147483647 ∧ x.c1.b.val<2147483647) :
 Canonical (toK (NFW_PreparedPort.q x)) := h

/-- The canonical raw claim returned by NGY is ported without changing limbs. -/
theorem claim (x : NFN_LPi_FieldValues.NE) (h : canonE x) :
 CanonicalWide (toE (NFW_PreparedPort.e (NFW_PowersCohort.toPublic x))) := by
 apply wide
 exact h
#print axioms wide
#print axioms qm
#print axioms claim
end AspisR1.NHS_CanonicalPorts
