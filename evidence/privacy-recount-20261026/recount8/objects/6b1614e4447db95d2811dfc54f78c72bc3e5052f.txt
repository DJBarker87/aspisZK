import R1Z.PV_CB_OwnedEncoder
import R1Z.PV_CBL_ArrayStep
import R1Z.PV_CBL_ArrayReadValue
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_EncoderMutation
set_option autoImplicit false

theorem read {E : Type} [Inhabited E] (out : Array E 512#usize) (j : Usize)
    (h : j.val<(512#usize).val) :
    Array.index_usize out j=ok out.val[j.val]! :=
  PV_CBL_ArrayReadValue.read out j h

/-- Every cell returns the changed array; there is no discarded borrowed
restoration continuation in this emitted body. -/
theorem restoration {E : Type} [Inhabited E] (inst : aspis_core.r0.scalar.CodeField E)
    (out : Array E 512#usize) (width j : Usize) (factor product : E)
    (hr : j.val<(512#usize).val) (hw : (Usize.wrapping_add width j).val<(512#usize).val)
    (hm : inst.mul out.val[j.val]! factor=ok product) :
    PV_CB_OwnedEncoder.owned.basis_cell inst out width j factor=
      ok (out.set (Usize.wrapping_add width j) product) := by
  simp only [PV_CB_OwnedEncoder.owned.basis_cell,read out j hr,hm,
    lift,bind_tc_ok,PV_CBL_ArrayStep.write out _ product hw]

/-- The fixture used by native differential validation changes ONE to TWO.
Only one cell is evaluated; no concrete recurrence is normalized. -/
theorem changed_cell (inst : aspis_core.r0.scalar.CodeField Nat)
    (hm : inst.mul 1 2=ok 2) :
    PV_CB_OwnedEncoder.owned.basis_cell inst (Array.repeat 512#usize 1)
      1#usize 0#usize 2=
      ok ((Array.repeat 512#usize 1).set (Usize.wrapping_add 1#usize 0#usize) 2) := by
  apply restoration inst _ _ _ _ _ (by change 0<512;decide) (by
    rw [Usize.wrapping_add_val_eq]
    change (1+0)%UScalar.size .Usize<512
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by decide))
  change inst.mul 1 2=ok 2
  exact hm

#print axioms read
#print axioms restoration
#print axioms changed_cell
end R1Z.PV_DL_EncoderMutation
