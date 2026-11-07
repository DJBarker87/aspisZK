import NMN_064
import NLW_StartScope
set_option autoImplicit false
noncomputable section
namespace NMN_CallerDomain
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
/-- This support lemma consumes only own-argument numeric scope and Root0.
It does not install a getter or assert child/headline success. -/
theorem of_scope {X : Type} (a : Args X)
 (scope : NLE_SafeCuts.Scope
  (NLE_CallerScope.metadata 0 0 0 a.publicBytes a.proof a.checkpoint))
 (root0 : NLP_InputDomain.Root0 a.checkpoint a.proof) : NMN_064.Domain a := by
 change a.publicBytes.val.length=1880 ∧ a.proof.val.length=57607 ∧
  a.checkpoint.val.length=1768 at scope
 exact ⟨scope.2.1,scope.2.2,by omega,root0⟩
/-- Encoder arrays always supply public1880, independently of parser success. -/
theorem public_bound (bytes : Array U8 1880#usize) : bytes.to_slice.val.length≤1880 := by
 have same := NLE_Length.public_extent bytes
 omega
#print of_scope
#print public_bound
#print axioms of_scope
#print axioms public_bound
end NMN_CallerDomain
