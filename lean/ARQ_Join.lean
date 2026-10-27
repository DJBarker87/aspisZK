import ARQ_Observer
import F3X_Join
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_Join
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment F3T_ByteCarrier

/-- The direct-account target. This is a statement, NOT a proved theorem or
an adopted transport law. The left branch is literally the F3X raw equality;
the guard and single right-hand event refer to the original account.
The adversary, projections, installation and budget are fixed before H. -/
def Target {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (D : LiteralByteProtocol.Decoder) (a : Adversary A) (Q0 Q1 : Nat) : Prop :=
  ∀ H : Bytes → State,
    accepted (eval H (account c hashv copy allocator id a)).2 = true →
    eval H (F3T_Installed.source c hashv (input c (eval H (submission a)).2)) =
      eval H (F3_Model.verifier D (input c (eval H (submission a)).2)) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a)
        ARQ_Observer.project (ARQ_Observer.select c id)))

#check @Target
#check @F3X_Join.accepted_raw_join_or_collision
end AspisR1.ARQ_Join
end
