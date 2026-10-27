import RPz8_ARQ_AccountView
import RPz8_ARQ_PrefixRecovery
import RPz8_ARQ_SamplerPrefix
import RPz8_ARQ_ModelAccepted
import RPz8_SCG_RawRecovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_ObservedRecovery
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier SCE_Experiment

theorem agreement {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State)
    (modelAccepted : (eval H (original D (F3T_Canon.canon (lift c (submission a))))).2.2 = true)
    (common : ∃ tail, (eval H (account c hashv copy allocator id a)).1 =
      ((eval H a.first).1 ++
        (eval H (F3J_SamplerRun.program
          (F3T_Canon.canonInput (input c (submitted (eval H a.first).2))).proof 0 33
          (FS.emptyPrefix (input c (submitted (eval H a.first).2)).semantic.value))).1) ++ tail) :
    OraclePortRefineJoin.RecoveredInputAgreement (ARQ_AccountView.physical c hashv copy allocator id a H)
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a))))) := by
  let P := F3T_Canon.canon (lift c (submission a))
  let j := F3T_Canon.canonInput (input c (submitted (eval H a.first).2))
  let left := ARQ_AccountView.physical c hashv copy allocator id a H
  let right := view (eval H (original D P))
  let prior := (eval H a.first).1 ++ (eval H (F3J_SamplerRun.program j.proof 0 33 (FS.emptyPrefix j.semantic.value))).1
  obtain ⟨tailL,logL⟩ := common
  obtain ⟨tailR,modelLog⟩ := ARQ_SamplerPrefix.model D H j
  have logR : right.1 = prior ++ tailR := by
    dsimp only [right,P,view]
    rw [original_eval,F3T_Canon.canon_eval,lift_eval,submission_eval,modelLog,List.append_assoc]
  have pub : left.2.1.1 = right.2.1.1 := by
    dsimp only [left,right,ARQ_AccountView.physical,view,P]
    rw [original_eval,F3T_Canon.canon_eval,lift_eval,submission_eval]
  have proof : left.2.1.2 = right.2.1.2 := by
    dsimp only [left,right,ARQ_AccountView.physical,view,P]
    rw [original_eval,F3T_Canon.canon_eval,lift_eval,submission_eval]
  have valid : ∀ n, n ≤ 30 → LiteralTranscript.valid n (right.2.1.2 n) := by
    intro n small
    simpa only [right,view,P,original_eval] using
      F3T_CanonicalChecks.canonical_valid D (lift c (submission a)) H modelAccepted n (by omega)
  have reads : ∀ addr, FS2.Duplex.Read
      (eval H (RawCutProverCompiler.verifier D (fun _ _ => false) right.2.1.1 right.2.1.2)).1 addr →
      FS2.Duplex.Read prior addr := by
    intro addr read
    dsimp only [right,view] at read
    rw [original_eval,F3T_Canon.canon_eval,lift_eval,submission_eval,ARQ_SamplerPrefix.raw] at read
    change addr ∈ ((eval H a.first).1 ++ _).map Prod.fst
    rw [List.map_append]
    exact List.mem_append_right _ read
  have agree := ARQ_PrefixRecovery.agreement D H left right prior tailL tailR logL logR pub proof
    (FS.eval_consistent H (account c hashv copy allocator id a))
    (FS.eval_consistent H (original D P)) reads valid
  exact SCG_RawRecovery.trans left right _ agree
    (SCI_Recovery.model_agreement D (lift c (submission a)) H modelAccepted)

#print axioms agreement
end AspisR1.ARQ_ObservedRecovery
end
