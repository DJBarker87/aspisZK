import OraclePortRecoveredAcceptanceC6
import OraclePortStoredAccountingC4
import OraclePortStoredProjectionC4

/-! Bind the containing trace to the actual adaptive stored-proof experiment.
No fixed stored proof is chosen outside the prover or across oracle worlds. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortReachedRunC6
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

abbrev input (P : Prover) (H : Bytes → State) := (eval H P).2
abbrev transcript (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  (LiteralByteProtocol.protocol D).transcript H (input P H).statement (input P H).proof 33
abbrev reached (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  LiteralTranscript.erasePrefix (transcript D P H)
abbrev terminal (P : Prover) (H : Bytes → State) := LiteralTranscript.erase ((input P H).proof 33)
abbrev decision := OraclePortStoredDecisionDraftC4.decision
abbrev run (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  eval H (original D decision P)

theorem accepted (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run D P H).2.2 = true) :
    (eval H (decision (input P H).stored (reached D P H) (terminal P H))).2 = true := by
  rw [original_eval] at ha
  change (eval H (OraclePortExperiment.verifier D (decision (input P H).stored)
    (input P H).statement (input P H).proof)).2 = true at ha
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at ha
  exact ha

/-- Every terminal decision read occurs in this actual original log. -/
theorem decision_read (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (a : Bytes) (read : Read (eval H (decision (input P H).stored
      (reached D P H) (terminal P H))).1 a) : Read (run D P H).1 a := by
  change Read (eval H (original D decision P)).1 a
  rw [original_eval]
  change Read ((eval H P).1 ++ (eval H (OraclePortExperiment.verifier D
    (decision (input P H).stored) (input P H).statement (input P H).proof)).1) a
  rw [OracleDecisionFeasibilityBudget.verifier_eval]
  simp only [Read,List.map_append,List.mem_append]
  exact Or.inr (Or.inr read)

/-- The selected multiproof reads are in the actual log; no containing trace
is supplied independently of the accepted experiment. -/
theorem slots_read (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run D P H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortStoredParserC4.parseReached (input P H).stored (reached D P H) = some p)
    (query : queries (reached D P H) = some q) :
    ∀ a, Read (eval H (verifySlots p q slots)).1 a → Read (run D P H).1 a := by
  obtain ⟨guard,p',q',i,hp,hq,pad,_,_,_⟩ :=
    OraclePortStoredDecisionDraftC4.accepted _ _ _ H (accepted D P H ha)
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
  intro a read
  apply decision_read D P H a
  simpa only [decision,OraclePortStoredDecisionDraftC4.decision,if_pos guard,parsed,query,
    if_pos pad,eval_bind,eval,List.append_nil] using read

theorem consistent (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    ∀ a ∈ (run D P H).1, a.2 = H a.1 := FS.eval_consistent H _

theorem distinct_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    firstReads emptyTable (run D P H).1 ≤ Q+1161 := by
  have h := OraclePortStoredAccountingC4.distinct_bound D decision
    (BinCompiledRunWordStability.wordsFromRun D) P Q hq
    OraclePortStoredDecisionDraftC4.decision_budget H
  rw [OraclePortStoredExperimentC4.first_reads] at h
  exact h

/-- All three commitment frames, and every other sampler frame, were read. -/
theorem frame_read (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (row : Nat) (bound : row < 33) :
    Read (run D P H).1 (RawCutWordsFromView.frameFromView D (view (run D P H)) row) := by
  rw [OraclePortStoredProjectionC4.frame_eq D decision P H row (by omega)]
  change Read (eval H (original D decision P)).1 _
  rw [original_eval]
  simp only [Read,List.map_append,List.mem_append]
  apply Or.inr
  exact OraclePortReplay.sampler_reads D (decision (input P H).stored) H
    (input P H).statement (input P H).proof _
      (OraclePortReplay.frame_in_sampler D H _ _ row bound)

#print axioms accepted
#print axioms decision_read
#print axioms slots_read
#print axioms consistent
#print axioms distinct_bound
#print axioms frame_read
end AspisR1.OraclePortReachedRunC6
end
