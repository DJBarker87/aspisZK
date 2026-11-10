import NPH_R22Weak
import AspisR1CanonicalQRawUnified.Funs
import FIo_QRawFuns
import JGi_QRawSourceForwardTotalityV1
import AspisR1QueryGeometryActual.Funs
import RPz7_FIo_NativeFuns

/-! NPH_ (R22, continuation items 2 and 3).
(2) FIo_QRaw.canonical.Q.raw is definitionally the AspisR1CanonicalQRawUnified body (same
normalised text, closure types are both `Unit`), so the closure theorem
AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs transfers to it.
(3) Arithmetic-safety of the checked shifts in fast_domain.fibre_point (`index >>> 9#i32`,
every index) and transport row_loop.body (`j >>> 2d` for d < 16; `x <<< 2t` for t < 32).
For these two bodies every other step is an array index, an iterator step, a pure bit
operation, an explicit wrapping_mul or a callback: none is integer-overflow-checked, so they
behave identically under overflow checks ON and OFF; R22 needs only the shifts. -/
set_option autoImplicit false
namespace AspisR1.NPH_R22QRawShift
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef

theorem qraw_eq (self rhs : FIo_QRaw.canonical.Q) :
    FIo_QRaw.canonical.Q.raw self rhs = AspisR1CanonicalQRawUnified.canonical.Q.raw self rhs := by
  with_unfolding_all rfl

theorem fio_qraw_total_of_canonical_limbs (self rhs : FIo_QRaw.canonical.Q)
    (hself0 : self.val[0]!.val ≤ 2^31-2) (hself1 : self.val[1]!.val ≤ 2^31-2)
    (hself2 : self.val[2]!.val ≤ 2^31-2) (hself3 : self.val[3]!.val ≤ 2^31-2)
    (hrhs0 : rhs.val[0]!.val ≤ 2^31-2) (hrhs1 : rhs.val[1]!.val ≤ 2^31-2)
    (hrhs2 : rhs.val[2]!.val ≤ 2^31-2) (hrhs3 : rhs.val[3]!.val ≤ 2^31-2) :
    ∃ out : Array Std.U64 4#usize, FIo_QRaw.canonical.Q.raw self rhs = .ok out := by
  rw [qraw_eq]
  exact AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs self rhs
    hself0 hself1 hself2 hself3 hrhs0 hrhs1 hrhs2 hrhs3

theorem numBits_ge : 32 ≤ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> omega

/-- fibre_point's only checked arithmetic step succeeds for every index. -/
theorem fibre_shift_ok (index : Usize) : ∃ z, (index >>> 9#i32 : Result Usize) = ok z := by
  have hb := numBits_ge
  obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (Usize.ShiftRight_IScalar_spec index 9#i32 (by decide)
    (by change (9 : Int) < (System.Platform.numBits : Int); omega))
  exact ⟨z, hz⟩

theorem shr_usize_ok (j s : Usize) (hs : s.val < 32) : ∃ z, (j >>> s : Result Usize) = ok z := by
  have hb := numBits_ge
  obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (UScalar.ShiftRight_spec j s (by
    change s.val < UScalarTy.numBits .Usize; simp only [UScalarTy.numBits]; omega))
  exact ⟨z, hz⟩

theorem shl_usize_ok (j s : Usize) (hs : s.val < 32) : ∃ z, (j <<< s : Result Usize) = ok z := by
  have hb := numBits_ge
  have hlt : s.val < UScalarTy.numBits .Usize := by simp only [UScalarTy.numBits]; omega
  obtain ⟨z, hz, _⟩ := WP.spec_imp_exists (UScalar.ShiftLeft_spec j s _ hlt rfl)
  exact ⟨z, hz⟩

theorem wmul2_val (d : Usize) (hd : d.val < 16) : (Std.Usize.wrapping_mul 2#usize d).val = 2 * d.val := by
  have hb := numBits_ge
  have h2 : (2#usize : Usize).val = 2 := by first | rfl | simp
  have key : 2 * d.val < 2 ^ 32 := by omega
  first
  | (rw [UScalar.wrapping_mul_val_eq, h2]; apply Nat.mod_eq_of_lt
     exact Nat.lt_of_lt_of_le key (Nat.pow_le_pow_right (by decide) (by first | omega | (simp only [UScalarTy.numBits]; omega))))
  | (rw [Usize.wrapping_mul_val_eq, h2]; apply Nat.mod_eq_of_lt
     exact Nat.lt_of_lt_of_le key (Nat.pow_le_pow_right (by decide) (by first | omega | (simp only [UScalarTy.numBits]; omega))))

/-- row_loop.body, first checked shift: safe for every loop index d < 16 (the reached domain
iter.end ≤ 16, PCQH-C5/NPE_). -/
theorem row_shr_ok (j d : Usize) (hd : d.val < 16) :
    ∃ z, (j >>> Std.Usize.wrapping_mul 2#usize d : Result Usize) = ok z :=
  shr_usize_ok j _ (by rw [wmul2_val d hd]; omega)

/-- row_loop.body, second checked shift: safe whenever the TAU entry read is below 16. -/
theorem row_shl_ok (x t : Usize) (ht : t.val < 16) :
    ∃ z, (x <<< Std.Usize.wrapping_mul 2#usize t : Result Usize) = ok z :=
  shl_usize_ok x _ (by rw [wmul2_val t ht]; omega)

#print axioms qraw_eq
#print axioms fio_qraw_total_of_canonical_limbs
#print axioms fibre_shift_ok
#print axioms row_shr_ok
#print axioms row_shl_ok
end AspisR1.NPH_R22QRawShift
