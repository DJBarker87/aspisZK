import NBB_Phase
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_Arithmetic
/-- Exact integer add/product fragment on the same canonical/phase domain. -/
theorem add (raw : U64) (limb basis : U32) (terms : Nat)
 (hl : limb.val<2^31-1) (hb : basis.val<2^31-1)
 (hr : NBB_Phase.Bound terms raw.val) :
 ∃ out : U64, S7OwnedP6Scalar.residue_scalar_owned raw limb basis false=ok out ∧
 out.val=raw.val+limb.val*basis.val := by
 have safe := S7OwnedP6ScalarProof.phase_bound raw limb basis (terms%4)
  (Nat.mod_lt _ (by decide)) hl hb hr
 obtain ⟨out,run,value⟩ := S7OwnedP6ScalarProof.scalar_success raw limb basis false safe
 exact ⟨out,run,value⟩
/-- The exact bit-fold fragment is total for every U64 input. -/
theorem fold (x : U64) : ∃ out : U64,
 AspisR1.ExtractedCurrentReducer.foldExecution x=ok out ∧
 out.val=AspisV8R17.RawReducer.foldBits x.val := by
 exact AspisR1.ExtractedCurrentReducer.foldExecution_success x
#print axioms add
#print axioms fold
end NBB_Arithmetic
