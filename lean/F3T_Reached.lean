import F3T_Trace
import F3T_Frame
import F3T_Bounds
import OraclePortFrozenOrderChecks
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Reached
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open F3T_Experiment OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortFrozenOrder (slotPrograms)

abbrev input (P : Prover) (H : Bytes → State) := (eval H P).2
abbrev transcript (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  (LiteralByteProtocol.protocol D).transcript H (input P H).semantic.value (input P H).proof 33
abbrev reached (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  LiteralTranscript.erasePrefix (transcript D P H)
abbrev terminal (P : Prover) (H : Bytes → State) := LiteralTranscript.erase ((input P H).proof 33)
abbrev decision (i : F3_Model.Input) := F3_Model.decision i.physical i.stored
abbrev run (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :=
  eval H (original D P)

theorem accepted (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run D P H).2.2 = true) :
    (eval H (decision (input P H) (reached D P H) (terminal P H))).2 = true := by
  change (eval H (original D P)).2.2 = true at ha
  rw [original_eval] at ha
  change (eval H (OraclePortExperiment.verifier D (decision (input P H))
    (input P H).semantic.value (input P H).proof)).2 = true at ha
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at ha
  exact ha

/-- Every terminal decision read occurs in this actual original log. -/
theorem decision_read (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (a : Bytes) (read : Read (eval H (decision (input P H)
      (reached D P H) (terminal P H))).1 a) : Read (run D P H).1 a := by
  change Read (eval H (original D P)).1 a
  rw [original_eval]
  change Read ((eval H P).1 ++ (eval H (OraclePortExperiment.verifier D
    (decision (input P H)) (input P H).semantic.value (input P H).proof)).1) a
  rw [OracleDecisionFeasibilityBudget.verifier_eval]
  simp only [Read,List.map_append,List.mem_append]
  exact Or.inr (Or.inr read)

/-- The selected multiproof reads are in the actual log; no containing trace
is supplied independently of the accepted experiment. -/
theorem slots_read (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (ha : (run D P H).2.2 = true) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : OraclePortStoredParserC4.parseReached (input P H).stored (reached D P H) = some p)
    (query : queries (reached D P H) = some q) :
    ∀ a, Read (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).1 a → Read (run D P H).1 a := by
  obtain ⟨guard,p',q',i,hp,hq,_,_,_⟩ :=
    F3T_Decision.accepted_details (input P H).physical _ _ _ H (accepted D P H ha)
  have psame : p' = p := Option.some.inj (hp.symm.trans parsed)
  have qsame : q' = q := Option.some.inj (hq.symm.trans query)
  subst p'; subst q'
  intro a read
  apply decision_read D P H a
  apply F3T_Trace.old_read H (input P H).physical _ _ _ (accepted D P H ha) a
  simpa only [OraclePortFrozenOrder.dV_frozen,if_pos guard,parsed,query,
    eval_bind,eval,List.append_nil] using read


theorem consistent (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    ∀ a ∈ (run D P H).1, a.2 = H a.1 := FS.eval_consistent H _

theorem distinct_bound (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    firstReads emptyTable (run D P H).1 ≤ Q+1161 := by
  have h := F3T_Bounds.distinct_bound D (BinCompiledRunWordStability.wordsFromRun D) P Q hq H
  rw [F3T_Bounds.first_reads] at h
  exact h

/-- All three commitment frames, and every other sampler frame, were read. -/
theorem frame_read (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (row : Nat) (bound : row < 33) :
    Read (run D P H).1 (RawCutWordsFromView.frameFromView D (view (run D P H)) row) := by
  rw [F3T_Frame.frame_eq D P H row (by omega)]
  change Read (eval H (original D P)).1 _
  rw [original_eval]
  simp only [Read,List.map_append,List.mem_append]
  apply Or.inr
  exact OraclePortReplay.sampler_reads D (decision (input P H)) H
    (input P H).semantic.value (input P H).proof _
      (OraclePortReplay.frame_in_sampler D H _ _ row bound)

#print axioms accepted
#print axioms decision_read
#print axioms slots_read
#print axioms consistent
#print axioms distinct_bound
#print axioms frame_read
end AspisR1.F3T_Reached
end
