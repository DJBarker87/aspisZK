import AspisR1CanonicalQRawUnified.Funs
import JGi_QRawCheckedMultiplyTotalityV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
open AspisR1CanonicalQRawUnified

namespace AspisR1S5QRawTotality

private theorem p_val : canonical.P.val = 2147483647 := by
  norm_num [canonical.P, UScalar.ofNatCore_val_eq]

private theorem pp_mask_val :
    (UScalar.cast UScalarTy.U64 canonical.P).val = 2147483647 := by
  rw [UScalar.cast_val_eq, p_val]
  exact Nat.mod_eq_of_lt (by norm_num)

/-- The generated checked `PP = P * P` subcall is total and returns its exact
integer value. This is the first source subcall instantiated from the generic
checked-multiply witness. -/
theorem pp_total :
    ∃ out : UScalar UScalarTy.U64,
      canonical.Q.raw.PP = .ok out ∧ out.val = 2147483647 * 2147483647 := by
  let p : UScalar UScalarTy.U64 := UScalar.cast .U64 canonical.P
  have hpval : p.val = 2147483647 := pp_mask_val
  have hmax : p.val * p.val ≤ UScalar.max UScalarTy.U64 := by
    rw [hpval, UScalar.max]
    norm_num [UScalarTy.U64_numBits_eq]
  obtain ⟨out, hmul, hout⟩ := u64_mul_total_of_le p p hmax
  have hcast : lift (UScalar.cast UScalarTy.U64 canonical.P) = .ok p := rfl
  refine ⟨out, ?_, ?_⟩
  · unfold canonical.Q.raw.PP
    rw [hcast]
    simp only [Aeneas.Std.bind_tc_ok]
    exact hmul
  · simpa [hpval] using hout

#print axioms pp_total
end AspisR1S5QRawTotality
