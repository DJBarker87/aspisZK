import SCI_Recovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_ModelAccepted
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier

theorem original {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver) (H : Bytes → State)
    (source : (eval H (F3T_Installed.source c hashv (input c (eval H P).2))).2 = true)
    (raw : eval H (F3T_Installed.source c hashv (input c (eval H P).2)) =
      eval H (F3_Model.verifier D (input c (eval H P).2))) :
    (eval H (F3T_Experiment.original D (F3T_Canon.canon (lift c P)))).2.2 = true := by
  rw [original_eval,F3T_Canon.canon_eval,lift_eval,F3T_Canon.verifier_canon,←raw]
  exact source

theorem projected (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (success : (eval H (F3T_Experiment.original D P)).2.2 = true) :
    (eval H (F3T_Charged.projected D P)).2.2 = true := by
  rw [F3T_Charged.projected_eval,recorded_eval]
  exact success

#print axioms original
#print axioms projected
end AspisR1.ARQ_ModelAccepted
end
