import R1Z.PV_CompressSuffix
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CompressModel
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6CompressControl
variable [ExternalTypes] [ExternalFuns]
-- This is the exact owned reference/model equation, not shipped op223.
theorem loop (values : Slice M) (lambda out power : Q) (i : Usize)
    (bound : i.val ≤ (Slice.len values).val) :
    ProverRwP6CompressSource.compress_loop values lambda out power i =
      PV_CompressList.fold (values.val.drop i.val) lambda out power := by
  exact (ProverRwP6CompressControl.loop_finite values lambda
    ((Slice.len values).val-i.val) out power i (by omega)).trans
      (PV_CompressSuffix.finite values lambda _ out power i (by omega))

theorem compress (tag : M) (values : Slice M) (lambda : Q) :
    ProverRwP6CompressSource.compress tag values lambda = (do
      let c ← aspis_core.field.CM31.from_m31 tag
      let out ← aspis_core.field.QM31.from_cm31 c
      PV_CompressList.fold values.val lambda out lambda) := by
  unfold ProverRwP6CompressSource.compress
  repeat' first | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr; intro _ _
  rw [loop values lambda _ _ 0#usize (by change 0≤_; omega)]
  rfl
#print axioms loop
#print axioms compress
end R1Z.PV_CompressModel
