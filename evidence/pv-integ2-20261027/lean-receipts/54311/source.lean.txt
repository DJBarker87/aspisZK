import R1Z.PV_CB_EncoderFill
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_EncoderRound
open Aeneas Aeneas.Std Result ProverRwFull ProverRwSuccessArithmeticTotal

def next_width (width : Usize) : Usize := Usize.wrapping_mul width 2#usize
theorem half_rank (width : Usize) (fuel : Nat) (rank : width.val*2^(fuel+1)=512) :
    2*width.val≤512 := by
  have hp := Nat.two_pow_pos fuel
  have hr : (width.val*2)*2^fuel=512 := by
    simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using rank
  have h := Nat.mul_le_mul_left (width.val*2) (show 1≤2^fuel by omega)
  simp only [Nat.mul_one,hr] at h
  omega
theorem next_value (width : Usize) (half : 2*width.val≤512) :
    (next_width width).val = width.val*2 := by
  rw [next_width,Usize.wrapping_mul_val_eq]
  change (width.val*2)%UScalar.size .Usize=width.val*2
  apply Nat.mod_eq_of_lt
  have big := (512#usize).hSize
  change 512<UScalar.size .Usize at big
  omega
theorem next_rank (width : Usize) (fuel : Nat) (rank : width.val*2^(fuel+1)=512) :
    (next_width width).val*2^fuel=512 := by
  rw [next_value width (half_rank width fuel rank)]
  simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using rank

theorem total {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (one_total : Total inst.ONE)
    (mul_total : ∀ a b,Total (inst.mul a b))
    (add_total : ∀ a b,Total (inst.add a b))
    (sub_total : ∀ a b,Total (inst.sub a b))
    (fuel : Nat) (width : Usize) (factor : E) (out : Array E 512#usize)
    (positive : 0<width.val) (rank : width.val*2^fuel=512) :
    Total (PV_CB_OwnedEncoder.owned.basis_round inst out width factor) := by
  change ∃ result,PV_CB_OwnedEncoder.owned.basis_round inst out width factor=.ok result
  induction fuel generalizing width factor out with
  | zero =>
    simp only [Nat.pow_zero,Nat.mul_one] at rank
    have done : ¬width<512#usize := by change ¬width.val<512;omega
    rw [PV_CB_OwnedEncoder.owned.basis_round]
    simp only [done,if_false]
    exact ⟨out,rfl⟩
  | succ fuel ih =>
    have half := half_rank width fuel rank
    have more : width<512#usize := by change width.val<512;omega
    have value := next_value width half
    obtain ⟨filled,hfilled⟩ := PV_CB_EncoderFill.total inst mul_total width factor out half
    obtain ⟨square,hsquare⟩ := mul_total factor factor
    obtain ⟨doubled,hdoubled⟩ := add_total square square
    obtain ⟨one,hone⟩ := one_total
    obtain ⟨next,hnext⟩ := sub_total doubled one
    obtain ⟨result,hresult⟩ := ih (next_width width) next filled (by omega) (next_rank width fuel rank)
    refine ⟨result,?_⟩
    rw [PV_CB_OwnedEncoder.owned.basis_round]
    simp only [more,if_true,hfilled,hsquare,lift,bind_tc_ok,hdoubled,hone,hnext]
    exact hresult
#print axioms half_rank
#print axioms next_value
#print axioms next_rank
#print axioms total
end R1Z.PV_CB_EncoderRound
