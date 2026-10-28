import R1Z.PV_RDB2_SumOriginal
import R1Z.PV_RDB2_Fold
import R1Z.PV_RDB2_ActualCarrier230
import R1Z.PV_RDB2_Transport
import R1Z.PV_RDB2_FullExternalFuns

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDB2_SumDeployed
open Aeneas Aeneas.Std Result PV_B1_230 PV_B1_SumControl

theorem fold_value (xs : List Q) (acc : Q) :
    PV_RDB2_Fold.fold aspis_core.field.QM31.add xs acc =
      ok (xs.foldl PV_B1_SumNative.add acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [PV_RDB2_Fold.fold,PV_B1_SumNative.add_source,bind_tc_ok,
      List.foldl_cons,ih]

/-- Operational interpretation of the original then/copied/fold body. The
backing slice is retained even though the consumed iterator is local. -/
def deployed (h1 : Slice Q) : Result (Option Q × List Q) :=
  if Slice.len h1 = 1024#usize then do
    let (sum,storage) ← PV_RDB2_Fold.run aspis_core.field.QM31.add h1.val
      h1.val.length 0 aspis_core.field.QM31.ZERO
    ok (some sum,storage)
  else ok (none,h1.val)

theorem complete (h1 : Slice Q) :
    deployed h1 = (do
      let value ← state_only_copy_helper_sum h1
      ok (value,h1.val)) := by
  by_cases h : Slice.len h1 = 1024#usize
  · rw [deployed,if_pos h,PV_RDB2_Fold.initial,fold_value,
      PV_B1_SumOriginal.exact_length h1 h]
    rfl
  · rw [deployed,if_neg h,PV_B1_SumOriginal.wrong_length h1 h]
    rfl

theorem storage_and_value (h1 : Slice Q) :
    deployed h1 = ok (PV_B1_SumOriginal.original_row h1,h1.val) := by
  rw [complete,PV_B1_SumOriginal.op230_source]
  rfl

theorem wrong_length_no_read (h1 : Slice Q) (h : Slice.len h1 ≠ 1024#usize) :
    deployed h1 = ok (none,h1.val) := if_neg h

open ProverRwFull PV_B1_Transport
variable [ExternalTypes]
abbrev HQ := ProverRwFull.aspis_core.field.QM31

def helper (xs : Slice HQ) : Result (Option HQ) :=
  resultMap (Option.map PV_B1_ActualCarrier230.fromQ)
    (PV_B1_230.state_only_copy_helper_sum (sliceMap PV_B1_ActualCarrier230.toQ xs))

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns := {ops with op230 := helper}

theorem installed (ops : ExternalFuns) (xs : Slice HQ) :
    (selected ops).op230 xs =
      ok (Option.map PV_B1_ActualCarrier230.fromQ
        (PV_B1_SumOriginal.original_row (sliceMap PV_B1_ActualCarrier230.toQ xs))) := by
  change helper xs = _
  unfold helper
  rw [PV_B1_SumOriginal.op230_source]
  rfl

theorem compressor_retained (ops : ExternalFuns) : (selected ops).op223 = ops.op223 := rfl

#print axioms fold_value
#print axioms complete
#print axioms storage_and_value
#print axioms wrong_length_no_read
#print axioms installed
#print axioms compressor_retained
end R1Z.PV_RDB2_SumDeployed
