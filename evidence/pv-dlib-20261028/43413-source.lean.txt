import R1Z.PV_DL_EncoderNative
import R1Z.PV_DL_EncoderMutation
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderBounds
set_option autoImplicit false

theorem cells (width j : Nat) (half : 2*width≤512) (inside : j<width) :
    j<512 ∧ width+j<512 ∧ min width (512-width)=width := by
  exact ⟨by omega,by omega,PV_DL_EncoderBasis.native_min width half⟩

theorem target_val (width j : Usize) (half : 2*width.val≤512)
    (inside : j.val<width.val) :
    (Usize.wrapping_add width j).val=width.val+j.val := by
  rw [Usize.wrapping_add_val_eq]
  change (width.val+j.val)%UScalar.size .Usize=width.val+j.val
  apply Nat.mod_eq_of_lt
  have big := (512#usize).hSize
  change 512<UScalar.size .Usize at big
  have h := (cells width.val j.val half inside).2.1
  omega

theorem writes {E : Type} [Inhabited E]
    (inst : aspis_core.r0.scalar.CodeField E) (out : Array E 512#usize)
    (width j : Usize) (factor product : E) (half : 2*width.val≤512)
    (inside : j.val<width.val) (hm : inst.mul out.val[j.val]! factor=ok product) :
    PV_CB_OwnedEncoder.owned.basis_cell inst out width j factor=
      ok (out.set (Usize.wrapping_add width j) product) := by
  apply PV_DL_EncoderMutation.restoration inst out width j factor product
  · exact (cells width.val j.val half inside).1
  · rw [target_val width j half inside]
    exact (cells width.val j.val half inside).2.1
  · exact hm

#print axioms cells
#print axioms target_val
#print axioms writes
end R1Z.PV_DL_EncoderBounds
