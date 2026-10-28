import NBC_Audit
import CheckpointBytes4Ops
import Port4A_ReaderInstall
import AspisR1PublicPreparation.Funs
set_option autoImplicit false
noncomputable section
namespace NBG_Transport
open Aeneas Aeneas.Std Result
abbrev V := AspisR1PublicPreparation.transport.Variant
abbrev CV := AspisR1Stage2.transport.Variant

def port : V → CV
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def folds : V → Usize
  | .S1 => 1#usize | .S2 => 2#usize | .D => 2#usize

theorem folds_result (v : V) :
    AspisR1PublicPreparation.transport.Variant.folds v = ok (folds v) := by
  cases v <;> simp [AspisR1PublicPreparation.transport.Variant.folds,
    AspisR1PublicPreparation.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    read_discriminant, AspisR1PublicPreparation.transport.Variant.read_discriminant, folds]

theorem tag_result (v : V) :
    AspisR1PublicPreparation.transport.Variant.tag v =
      AspisR1.CheckpointBytes4Ops.tag (port v) := by
  cases v <;> rfl

theorem final_len_result (v : V) :
    AspisR1.CheckpointBytes4Ops.finalLen (port v) =
      ok (match v with | .S1 => 256#usize | .S2 => 64#usize | .D => 64#usize) := by
  cases v <;> rfl

theorem checkpoint_size_result (v : V) :
    AspisR1.CheckpointBytes4Ops.checkpointSize (port v) =
      ok (match v with | .S1 => 4840#usize | .S2 => 1768#usize | .D => 1768#usize) := by
  cases v <;> simp only [AspisR1.CheckpointBytes4Ops.checkpointSize,
    AspisR1.CheckpointBytes4Ops.finalLen, port, bind_tc_ok] <;>
    rw [AspisR1.Port4A_ReaderInstall.mul_value _ _ (by decide), bind_tc_ok,
      AspisR1.Port4A_ReaderInstall.add_value _ _ (by decide)] <;> rfl

#print axioms folds_result
#print axioms tag_result
#print axioms final_len_result
#print axioms checkpoint_size_result
end NBG_Transport
