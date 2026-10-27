import R1Z.PV_RE_Increment0
import R1Z.PV_RE_RetryCongruence
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Increments
open Aeneas Aeneas.Std Result ProverRwFull

theorem inc1 : Aeneas.Std.lift (Usize.wrapping_add 1#usize 1#usize) = Result.ok 2#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 1 1

#print axioms inc1

theorem inc2 : Aeneas.Std.lift (Usize.wrapping_add 2#usize 1#usize) = Result.ok 3#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 2 1

#print axioms inc2

theorem inc3 : Aeneas.Std.lift (Usize.wrapping_add 3#usize 1#usize) = Result.ok 4#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 3 1

#print axioms inc3

theorem inc4 : Aeneas.Std.lift (Usize.wrapping_add 4#usize 1#usize) = Result.ok 5#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 4 1

#print axioms inc4

theorem inc5 : Aeneas.Std.lift (Usize.wrapping_add 5#usize 1#usize) = Result.ok 6#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 5 1

#print axioms inc5

theorem inc6 : Aeneas.Std.lift (Usize.wrapping_add 6#usize 1#usize) = Result.ok 7#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 6 1

#print axioms inc6

theorem inc7 : Aeneas.Std.lift (Usize.wrapping_add 7#usize 1#usize) = Result.ok 8#usize := by
  apply congrArg Result.ok
  apply (Usize.eq_equiv_bv_eq _ _).mpr
  unfold Usize.wrapping_add UScalar.wrapping_add
  simp only [Usize.ofNat_bv]
  exact BitVec.ofNat_add_ofNat 7 1

#print axioms inc7
end R1Z.PV_RE_Increments
