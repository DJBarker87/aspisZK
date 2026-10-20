import CuSavingsS2SourceControl
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceRowDigit
open Aeneas Aeneas.Std Result AspisR1S2Groups

def digit (j d out : Usize) : Result Usize := do
  let shift ← 2#usize*d
  let right ← j >>> shift
  let masked := right &&& 3#usize
  let tau ← Array.index_usize transport.TAU d
  let shift1 ← 2#usize*tau
  let left ← masked <<< shift1
  .ok (out ||| left)

theorem source_success (j d out : Usize) (hd : d.val < 5) :
    ∃ result : Usize, digit j d out = .ok result ∧
      result.val = out.val ||| (((j.val >>> (2*d.val)) &&& 3) <<<
        (2*CuSavingsS2Tables.tau.getD d.val 0)) := by
  have htwo : (2#usize).val=2 := by scalar_tac
  have hthree : (3#usize).val=3 := by scalar_tac
  have hbits : 32 ≤ System.Platform.numBits := System.Platform.le_numBits
  obtain ⟨shift,hs,hsv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=2#usize) (y:=d) (by scalar_tac))
  rw [htwo] at hsv
  obtain ⟨right,hr,hrv,_⟩ := WP.spec_imp_exists (Usize.ShiftRight_spec j shift (by omega))
  obtain ⟨tau,ht,htv,htb⟩ := CuSavingsS2SourceControl.tau_source d hd
  obtain ⟨shift1,hs1,hs1v⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=2#usize) (y:=tau) (by scalar_tac))
  rw [htwo] at hs1v
  let masked := right &&& 3#usize
  have hm : masked.val ≤ 3 := by
    change (right &&& 3#usize).val ≤ 3
    rw [UScalar.val_and,hthree]
    exact Nat.and_le_right
  have hpow : 2^shift1.val ≤ (2:Nat)^8 := Nat.pow_le_pow_right (by decide) (by omega)
  have hfit32 : (masked.val <<< shift1.val) < 2^32 := by
    rw [Nat.shiftLeft_eq]
    have hb := Nat.mul_le_mul hm hpow
    norm_num at hb ⊢
    omega
  have hsize : (2:Nat)^32 ≤ Usize.size := by
    simp only [Usize.size,Usize.numBits,UScalar.size,UScalarTy.numBits]
    exact Nat.pow_le_pow_right (by decide) hbits
  obtain ⟨left,hl,hlv,_⟩ := WP.spec_imp_exists (Usize.ShiftLeft_spec masked shift1 (by omega))
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hfit32 hsize)] at hlv
  dsimp only [masked] at hl
  refine ⟨out ||| left,?_,?_⟩
  · simp only [digit,hs,hr,ht,hs1,hl,bind_tc_ok]
  · rw [UScalar.val_or,hlv]
    dsimp only [masked]
    rw [UScalar.val_and,hthree,hrv,hsv,hs1v,htv]

#print axioms source_success
end AspisR1.CuSavingsS2SourceRowDigit
