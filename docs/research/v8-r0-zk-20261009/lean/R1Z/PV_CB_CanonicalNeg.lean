import R1Z.PV_CB_CanonicalM31Ops
import R1Z.PV_CB_CurrentNeg
import R1Z.ProverCommitNativeNeg49
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalNeg
open Aeneas Aeneas.Std Result PV_CB_CanonicalM31

theorem neg (input : U32) (valid : Valid input) :
    ∃ out, PV_CB_CurrentNeg.source input = ok out ∧ Valid out := by
  obtain ⟨out,hout,vout,_⟩ := ProverCommitNativeNeg49.neg_word input valid
  exact ⟨out,(PV_CB_CurrentNeg.native input).trans hout,vout⟩
#print axioms neg
end R1Z.PV_CB_CanonicalNeg
