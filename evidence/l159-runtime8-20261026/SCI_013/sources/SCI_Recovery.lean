import SCI_Projection
import SCF_Recovery
import SCE_ModelReadFrames
import SCE_ReplayExtractTransport
import SCE_Physical
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCI_Recovery
open FS FS2 FS2.Duplex
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier OraclePortRefineJoin

/-- Accepted frozen3 single-pass runs and the maintained two-pass experiment
have recovered-input agreement. All three read-cut conditions are DERIVED
from model acceptance; they are not new hypotheses on the account. -/
theorem model_agreement (D : LiteralByteProtocol.Decoder) (P : Prover)
    (H : Bytes → State)
    (success : (eval H (original D (F3T_Canon.canon P))).2.2 = true) :
    RecoveredInputAgreement (view (eval H (original D (F3T_Canon.canon P))))
      (eval H (F3T_Charged.projected D (F3T_Canon.canon P))) := by
  let CP := F3T_Canon.canon P
  let v := eval H (original D CP)
  let suffix := (eval H (F3_Model.verifier D v.2.1)).1
  let w := F3T_Charged.build D (view v)
  have shape : eval H (F3T_Charged.projected D CP) =
      SCE_ReplayFrames.annotated (view v) suffix w := by
    rw [F3T_Charged.projected_eval,F3T_Experiment.recorded_eval]
    rfl
  have consistent : ∀ q ∈ (view v).1 ++ suffix, q.2 = H q.1 := by
    intro q member
    rcases List.mem_append.mp member with first | second
    · exact FS.eval_consistent H (original D CP) q first
    · exact FS.eval_consistent H (F3_Model.verifier D v.2.1) q second
  have known : ∀ a ∈ suffix.map Prod.fst, a ∈ (view v).1.map Prod.fst := by
    dsimp only [suffix,v,view]
    rw [original_eval]
    dsimp only
    intro a member
    rw [List.map_append,List.mem_append]
    exact Or.inr member
  have frames := SCE_ModelReadFrames.frames D P H success
  change RecoveredInputAgreement (view v) _
  rw [shape]
  apply SCF_Recovery.agreement
  · rfl
  · intro row _
    exact (SCE_ReplayFrames.frame_same (view v) suffix w H consistent known row).symm
  · intro row selected
    rw [SCE_ReplayFrames.frame_same (view v) suffix w H consistent known row]
    change _ = BinRawByteCutRecovery.cut ((view v).1 ++ suffix) _
    apply Eq.symm
    apply SCE_ReplayTable.cut_append
    rcases selected with rfl | rfl | rfl
    · exact frames.1
    · exact frames.2.1
    · exact frames.2.2

/-- Concrete account recovery consumer. Log equality and model acceptance
are the outstanding A/B/source-join outputs, not adopted trust. The SCE
shared-adversary input projection supplies every input equality internally. -/
theorem account_agreement {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State) (run : RunView)
    (observed : (eval H (SCE_Experiment.runtime c hashv copy allocator id a)).2 = some run)
    (success : run.2.2 = true)
    (modelSuccess : (eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).2.2 = true)
    (ordered : run.1 =
      (eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).1) :
    RecoveredInputAgreement (view run)
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))) := by
  have same : run = eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a)))) := by
    apply Prod.ext ordered
    apply Prod.ext
    · rw [SCE_Projection.input_projection c hashv copy allocator id a H run observed,original_eval]
    · exact success.trans modelSuccess.symm
  rw [same]
  exact model_agreement D (lift c (SCE_Experiment.submission a)) H modelSuccess

/-- Each extractor coin tape is transported, without a separate executable
recovery hypothesis once the concrete single-pass join has been established. -/
theorem account_extract {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State) (run : RunView)
    (observed : (eval H (SCE_Experiment.runtime c hashv copy allocator id a)).2 = some run)
    (success : run.2.2 = true)
    (modelSuccess : (eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).2.2 = true)
    (ordered : run.1 =
      (eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).1)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract (view run) coins =
      RawRecordedPublicSpendExtractorBin.extract
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))) coins :=
  SCF_Recovery.extract _ _
    (account_agreement c D hashv copy allocator id a H run observed success modelSuccess ordered) coins

/-- The requested accepted F3X branch consumer, specialized to the concrete
same-adversary account. Source acceptance (A), its exact chronological source
join (B), and the pointwise raw F3X branch are the ONLY unproved inputs.
Canonicalization, observer input identity, model acceptance, the three causal
cuts and executable recovery are derived here. -/
theorem account_of_join {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : SCE_Experiment.Adversary A) (H : Bytes → State) (run : RunView)
    (observed : (eval H (SCE_Experiment.runtime c hashv copy allocator id a)).2 = some run)
    (success : run.2.2 = true)
    (sourceSuccess : (eval H (F3T_Installed.source c hashv
      (input c (eval H (SCE_Experiment.submission a)).2))).2 = true)
    (raw : eval H (F3T_Installed.source c hashv
      (input c (eval H (SCE_Experiment.submission a)).2)) =
      eval H (F3_Model.verifier D (input c (eval H (SCE_Experiment.submission a)).2)))
    (ordered : (eval H (SCE_Experiment.account c hashv copy allocator id a)).1 =
      (eval H a.first).1 ++ (eval H (F3T_Installed.source c hashv
        (input c (eval H (SCE_Experiment.submission a)).2))).1) :
    (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).2.2 = true ∧
    RecoveredInputAgreement (view run)
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))) := by
  have modelSuccess : (eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).2.2 = true := by
    rw [original_eval,F3T_Canon.canon_eval,lift_eval,F3T_Canon.verifier_canon,← raw]
    exact sourceSuccess
  have logs : run.1 = (eval H (original D (F3T_Canon.canon (lift c (SCE_Experiment.submission a))))).1 := by
    rw [SCE_Projection.chronological c hashv copy allocator id a H run observed,
      original_eval,F3T_Canon.canon_eval,lift_eval,F3T_Canon.verifier_canon,← raw]
    simpa only [SCE_Experiment.submission_eval] using ordered
  refine ⟨?_,account_agreement c D hashv copy allocator id a H run observed success modelSuccess logs⟩
  rw [F3T_Charged.projected_eval,recorded_eval]
  exact modelSuccess

#print axioms account_of_join
#print axioms model_agreement
#print axioms account_agreement
#print axioms account_extract
end AspisR1.SCI_Recovery
end
