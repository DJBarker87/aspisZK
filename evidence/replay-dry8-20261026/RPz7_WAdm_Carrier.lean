import RPz7_WAdm_WideCarrier
import RPz7_WAdm_Inventory
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Carrier
open Tx1Q_Carriers CheckpointBytes3Namespaces
open OraclePortCkptAbi2Extracted

/-- Fixed-array caller carriers used by the bounded native harness. Their
slice views are the original proof/public values, with no alternate bytes. -/
def proofArray (proof : Slice U8) (size : proof.val.length = 57607) : Array U8 57607#usize :=
  ⟨proof.val,size⟩
def publicArray (pub : Slice U8) (size : pub.val.length = 1880) : Array U8 1880#usize :=
  ⟨pub.val,size⟩

theorem proof_view (proof : Slice U8) (size : proof.val.length = 57607) :
    Array.to_slice (proofArray proof size) = proof := rfl

theorem public_view (pub : Slice U8) (size : pub.val.length = 1880) :
    Array.to_slice (publicArray pub size) = pub := rfl

/-- Private WideExact values in the actual certificate can be constructed
with exactly these raw limbs. No native output or native/source equality is
assumed. This is value-carrier admission, not a native heap-state theorem. -/
structure WideInputs (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator) : Prop where
  gamma : aspis_core.field.wide_exact.WideExact.from_limbs (WAdm_WideIndices.limbs (toE p.gamma)) = ok (some (toE p.gamma))
  kappa : aspis_core.field.wide_exact.WideExact.from_limbs (WAdm_WideIndices.limbs (toE p.kappa)) = ok (some (toE p.kappa))
  alpha : ∀ x ∈ p.alpha.val,
    aspis_core.field.wide_exact.WideExact.from_limbs (WAdm_WideIndices.limbs (toE x)) = ok (some (toE x))
  claim : aspis_core.field.wide_exact.WideExact.from_limbs (WAdm_WideIndices.limbs (toE p.claim)) = ok (some (toE p.claim))
  rhs : aspis_core.field.wide_exact.WideExact.from_limbs (WAdm_WideIndices.limbs (toE a.rhs)) = ok (some (toE a.rhs))

attribute [local irreducible] aspis_core.field.wide_exact.WideExact.from_limbs

theorem wide (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
    (proof pub : Slice U8) (domain : WAdm_Domain.Admitted p a proof pub) : WideInputs p a := by
  refine ⟨WAdm_WideCarrier.from_limbs _ domain.gamma,
    WAdm_WideCarrier.from_limbs _ domain.kappa,?_,
    WAdm_WideCarrier.from_limbs _ domain.claim,WAdm_WideCarrier.from_limbs _ domain.rhs⟩
  intro x member
  exact WAdm_WideCarrier.from_limbs _ (domain.alpha x member)

#print axioms proof_view
#print axioms public_view
#print axioms wide
#print WideInputs
end AspisR1.WAdm_Carrier
end
