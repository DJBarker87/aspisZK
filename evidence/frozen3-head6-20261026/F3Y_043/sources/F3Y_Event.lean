import F3U_CollisionJoin
import F3Y_Join
import F3U_CollisionJoin
import F3X_JointCongr
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Y_Event
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

def bad {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (prior : Program Bytes State Unit) (Q : Nat)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    F3U_CollisionJoin.Exception := fun H pub stored=>
  BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
    (eval H (Hiq_RecordedJoint.program (F3X_AccountPrior.program c hashv prior ⟨pub,stored⟩)
      F3X_Projection.project select))

theorem actual {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (P : ByteProver) (Q : Nat)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    bad c hashv (F3X_Account.prior P) Q select H (eval H P).2.publicBytes (eval H P).2.stored ↔
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P) F3X_Projection.project select)) := by
  unfold bad
  rw [F3X_JointCongr.evaluation _ _ F3X_Projection.project select H (F3X_AccountPrior.actual c hashv P H)]

#print axioms actual
end AspisR1.F3Y_Event
end
