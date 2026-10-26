import Rc7_Top
import Rc8_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.Rc8_Event
open Aeneas Aeneas.Std Result FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
/-- The binding alternative and the headline charge are one recorded event,
with no independence hypothesis and no extra union-bound term. -/
theorem single {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (P : F3T_ByteCarrier.ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    (∀ H, BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (F3X_Account.program (FIo_Install.configuration err c r) hashv P) F3X_Projection.project select)) ∨
      R9PoolRuntimeBinding.P2Prime H
        (select (eval H (F3X_Account.program (FIo_Install.configuration err c r) hashv P)).2).1
        (select (eval H (F3X_Account.program (FIo_Install.configuration err c r) hashv P)).2).2) ∧
    F3T_AccountCharge.mass (F3X_Account.program (FIo_Install.configuration err c r) hashv P)
      F3X_Projection.project select Q ≤ 6*((Q+2965:Nat):Rat)^2/(2:Rat)^256 := by
  exact P2P_Accounting.single_event _ F3X_Projection.project select Q
    (F3Y_AccountMass.budget (Rc2_Install.configuration (Rc5_Install.seed err (FIo_Install.select r c)) r) hashv D w P Q queries)
#print axioms single
end AspisR1.Rc8_Event
end
