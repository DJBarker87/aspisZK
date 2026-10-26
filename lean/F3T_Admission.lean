import F3T_Canon
import F3T_Charged
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Admission
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment
abbrev output (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  (eval H (recorded D (F3T_Charged.build D) P)).2.1
abbrev rows (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  ((LiteralByteProtocol.protocol D).transcript H
    (output D P H).semantic.value (output D P H).proof 33).rounds

theorem physical (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (output D P H).physical=(eval H P).2.physical := by
  unfold output
  rw [recorded_eval,original_eval]
  rfl

theorem semantic (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (output D P H).semantic=(eval H P).2.semantic := by
  unfold output
  rw [recorded_eval,original_eval]
  rfl

theorem stored (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (output D P H).stored=(eval H P).2.stored := by
  unfold output
  rw [recorded_eval,original_eval]
  rfl

#print axioms physical
#print axioms semantic
#print axioms stored
end AspisR1.F3T_Admission
end
