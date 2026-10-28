import R1Z.PV_DL_EncoderFill
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderBasis
set_option autoImplicit false

def advance (width : Usize) : Usize := Usize.wrapping_mul width 2#usize

theorem half_rank (width : Usize) (fuel : Nat) (rank : width.val*2^(fuel+1)=512) :
    2*width.val≤512 := by
  have hp := Nat.two_pow_pos fuel
  have hr : (width.val*2)*2^fuel=512 := by
    simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using rank
  have h := Nat.mul_le_mul_left (width.val*2) (show 1≤2^fuel by omega)
  simp only [Nat.mul_one,hr] at h
  omega

theorem advance_val (width : Usize) (half : 2*width.val≤512) :
    (advance width).val=width.val*2 := by
  rw [advance,Usize.wrapping_mul_val_eq]
  change (width.val*2)%UScalar.size .Usize=width.val*2
  apply Nat.mod_eq_of_lt
  have big := (512#usize).hSize
  change 512<UScalar.size .Usize at big
  omega

def factor {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (x : E) : Result E := do
  let square ← inst.mul x x
  let doubled ← inst.add square square
  let one ← inst.ONE
  inst.sub doubled one

def finite {E : Type} (inst : aspis_core.r0.scalar.CodeField E) :
    Nat → Array E 512#usize → Usize → E → Result (Array E 512#usize)
  | 0,out,_,_ => ok out
  | fuel+1,out,width,x => do
    let out ← PV_DL_EncoderFill.finite inst width x width.val 0#usize out
    let x ← factor inst x
    finite inst fuel out (advance width) x

theorem source {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (fuel : Nat) (out : Array E 512#usize) (width : Usize) (x : E)
    (positive : 0<width.val) (rank : width.val*2^fuel=512) :
    PV_CB_OwnedEncoder.owned.basis_round inst out width x=finite inst fuel out width x := by
  induction fuel generalizing out width x with
  | zero =>
    simp only [Nat.pow_zero,Nat.mul_one] at rank
    have done : ¬width<512#usize := by change ¬width.val<512;omega
    rw [PV_CB_OwnedEncoder.owned.basis_round]
    simp only [done,if_false,finite]
  | succ fuel ih =>
    have half := half_rank width fuel rank
    have more : width<512#usize := by change width.val<512;omega
    have hv := advance_val width half
    have hr : (advance width).val*2^fuel=512 := by
      rw [hv]
      simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using rank
    rw [PV_CB_OwnedEncoder.owned.basis_round]
    simp only [more,if_true,finite,factor,lift,bind_tc_ok,bind_assoc_eq]
    rw [PV_DL_EncoderFill.source inst width x width.val 0#usize out (by simp) (by omega)]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih _ (advance width) _ (by omega) hr

def value {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (x : E) : Result (Array E 512#usize) := do
  let one ← inst.ONE
  finite inst 9 (Array.repeat 512#usize one) 1#usize x

theorem basis_source {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (x : E) :
    PV_CB_OwnedEncoder.owned.basis inst x=value inst x := by
  unfold PV_CB_OwnedEncoder.owned.basis value
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro one hone
  exact source inst 9 _ 1#usize x (by decide) (by decide)

/-- All nine native basis rounds have width at most 256 before updating.
Thus `width.min(512-width)` in the native source is exactly `width`. -/
theorem native_min (width : Nat) (half : 2*width≤512) : min width (512-width)=width := by
  exact Nat.min_eq_left (by omega)

#print axioms advance
#print axioms half_rank
#print axioms advance_val
#print axioms factor
#print axioms finite
#print axioms source
#print axioms value
#print axioms basis_source
#print axioms native_min
end R1Z.PV_DL_EncoderBasis
