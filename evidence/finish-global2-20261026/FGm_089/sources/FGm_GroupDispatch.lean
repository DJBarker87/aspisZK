import FGm_GroupValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_GroupDispatch
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem same (w : FIo_Native.weights.Weights) (f : Slice U8) (low : Array NE 16#usize)
    (variant : w.variant=FIo_Native.transport.Variant.S2) (length : f.val.length=2048) :
    FIo_Native.weights.grouped_inactive_pair w f low=
      FIo_Native.weights.s2_grouped_inactive_pair f low := by
  have eqCall : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
      w.variant FIo_Native.transport.Variant.S2=ok true := by
    rw [variant]
    simp [FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq]
  have len : Slice.len f=2048#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val]
    change f.val.length=(2048#usize).val
    rw [length]
    scalar_tac
  have product : Usize.wrapping_mul 64#usize 32#usize=2048#usize := by
    apply UScalar.eq_of_val_eq
    have arithmetic : (64#usize).val*(32#usize).val=(2048#usize).val := by scalar_tac
    have bound : (2048#usize).val<UScalar.size .Usize := by
      simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using (2048#usize).bv.isLt
    rw [Usize.wrapping_mul_val_eq,arithmetic,Nat.mod_eq_of_lt bound]
  unfold FIo_Native.weights.grouped_inactive_pair
  rw [eqCall]
  simp only [bind_tc_ok,ite_true,lift]
  rw [len,product,if_pos rfl]

#print axioms same
end AspisR1.FGm_GroupDispatch
end
