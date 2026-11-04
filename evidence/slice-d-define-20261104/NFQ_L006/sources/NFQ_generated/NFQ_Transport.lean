import NFQ_Reference.Funs
import CheckpointBytes4Ops
import Port4A_ReaderInstall
import AspisR1PublicPreparation.Funs
set_option autoImplicit false
noncomputable section
namespace NFQ_Transport
open Aeneas Aeneas.Std Result
abbrev V := AspisR1PublicPreparation.transport.Variant
abbrev CV := AspisR1Stage2.transport.Variant
def code : V → U8
  | .S1 => 0#u8 | .S2 => 1#u8 | .D => 2#u8
def port : V → CV
  | .S1 => .S1 | .S2 => .S2 | .D => .D

theorem folds_reference (v : V) :
    NFQ_Reference.folds_ref (code v) =
      AspisR1PublicPreparation.transport.Variant.folds v := by
  cases v <;> simp [code, NFQ_Reference.folds_ref,
    AspisR1PublicPreparation.transport.Variant.folds,
    AspisR1PublicPreparation.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    read_discriminant, AspisR1PublicPreparation.transport.Variant.read_discriminant]

theorem final_len_reference (v : V) :
    NFQ_Reference.final_len_ref (code v) =
      AspisR1.CheckpointBytes4Ops.finalLen (port v) := by
  cases v <;> rfl

theorem checkpoint_size_reference (v : V) :
    NFQ_Reference.checkpoint_size_ref (code v) =
      AspisR1.CheckpointBytes4Ops.checkpointSize (port v) := by
  cases v <;> simp only [AspisR1.CheckpointBytes4Ops.checkpointSize,
    AspisR1.CheckpointBytes4Ops.finalLen, port, bind_tc_ok] <;>
    rw [AspisR1.Port4A_ReaderInstall.mul_value _ _ (by decide), bind_tc_ok,
      AspisR1.Port4A_ReaderInstall.add_value _ _ (by decide)] <;> rfl

#print axioms folds_reference
#print axioms final_len_reference
#print axioms checkpoint_size_reference
end NFQ_Transport
