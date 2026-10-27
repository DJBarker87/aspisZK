import Rc7_Event
import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc10_Clean
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
/-- The single charged alternative is not all worlds. This does not assert
joint inhabitation of the accepted native and global finish premises. -/
theorem exists_world {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : F3T_ByteCarrier.ByteProver)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ 0)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    ∃ H : Bytes → State, ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (0+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program (FIp_Install.configuration err c r) hashv P)
        F3X_Projection.project select)) :=
  F3Y_AccountMass.clean (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r) hashv D w P queries select
#print axioms exists_world
end AspisR1.Rc10_Clean
end
