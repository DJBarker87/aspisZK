import XSa_RawActual
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_DotWord

theorem update (s r : U64) : AspisR1DotPushLocal.Proof.updateWord s r =
 XRn_Join_u64 (s.val+XRn_Join_partial r.val) := by
 apply UScalar.eq_of_val_eq
 unfold AspisR1DotPushLocal.Proof.updateWord
 change (U64.wrapping_add s (AspisR1EbyKDotPushActualFoldV2.actualWrappingFold r)).val = _
 rw [U64.wrapping_add_val_eq,AspisR1EbyKDotPushActualFoldV2.actualWrappingFold_value]
 change (s.val+AspisR1EbyKDotPushNatStep.foldedRaw r.val)%18446744073709551616 =
   (s.val+(r.val%2147483648+r.val/2147483648)%18446744073709551616)%18446744073709551616
 unfold AspisR1EbyKDotPushNatStep.foldedRaw AspisR1EbyKDotPushNatStep.limbBase
 rw [Nat.add_mod,Nat.add_mod]
 simp only [Nat.mod_mod]

#print axioms update
end XSa_DotWord
