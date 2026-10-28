import R1Z.PV_RunJoin_PointMeaning34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SampleDomain34
open Aeneas Aeneas.Std Result

def remaining (r : Usize) := Usize.wrapping_sub 9#usize r
def assignments (r : Usize) := Usize.wrapping_shl 1#usize (UScalar.cast .U32 (remaining r))
def count (r : Usize) := Usize.wrapping_mul 28#usize (assignments r)

theorem remaining_value (r : Usize) (hr : r.val<10) : (remaining r).val=9-r.val :=
  ProverCommitSampleBits49.sub_value 9#usize r (by change r.val≤9;omega)

theorem assignments_value (r : Usize) (hr : r.val<10) :
    (assignments r).val=2^(9-r.val) := by
  have hc : (UScalar.cast .U32 (remaining r)).val=9-r.val := by
    have h := remaining_value r hr
    scalar_tac
  unfold assignments
  change ((1#usize).bv.shiftLeft ((UScalar.cast .U32 (remaining r)).val%UScalarTy.Usize.numBits)).toNat=_
  simp only [BitVec.shiftLeft_eq,BitVec.toNat_shiftLeft]
  have hbits : 32≤UScalarTy.Usize.numBits := System.Platform.le_numBits
  rw [hc,Nat.mod_eq_of_lt (by omega : 9-r.val<UScalarTy.Usize.numBits)]
  change (1 <<< (9-r.val))%2^UScalarTy.Usize.numBits=2^(9-r.val)
  rw [Nat.one_shiftLeft,Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]

theorem assignments_bound (r : Usize) (hr : r.val<10) :
    0<(assignments r).val ∧ (assignments r).val≤512 := by
  rw [assignments_value r hr]
  exact ⟨Nat.two_pow_pos _,by
    change 2^(9-r.val)≤2^9
    exact Nat.pow_le_pow_right (by decide) (by omega)⟩

/-- Actual worker count computation does not wrap in any valid round. -/
theorem count_value (r : Usize) (hr : r.val<10) :
    (count r).val=28*(assignments r).val := by
  unfold count
  rw [Usize.wrapping_mul_val_eq]
  change (28*(assignments r).val)%UScalar.size .Usize=28*(assignments r).val
  apply Nat.mod_eq_of_lt
  have hsize : 2^32≤UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  have hb := (assignments_bound r hr).2
  omega

/-- Every actual worker index gives one of 28 samples and an in-range
Boolean assignment. This discharges the arithmetic hypotheses of the
source point bridge, not the worker scheduler's effect/coverage law. -/
theorem domain (r i : Usize) (hr : r.val<10) (hi : i.val<(count r).val) :
    i.val/(assignments r).val<28 ∧ i.val%(assignments r).val<2^(9-r.val) := by
  have hp := (assignments_bound r hr).1
  rw [count_value r hr] at hi
  constructor
  · exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa only [Nat.mul_comm] using hi)
  · rw [← assignments_value r hr]
    exact Nat.mod_lt _ hp

#print axioms remaining_value
#print axioms assignments_value
#print axioms assignments_bound
#print axioms count_value
#print axioms domain
end R1Z.PV_RunJoin_SampleDomain34
