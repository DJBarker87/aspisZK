import OracleDecisionPrereqSampler
import AspisRec40HitMass
import AspisLib_QueryAccounting

/-! Aspis 40-row verifier: the digest-call budget of the transcript part, and
the issued-call / distinct-read bounds the collision envelope needs.

R1's transcript count is `OracleDecisionPrereqSampler`: per row
`rowBudget n = 3 + [n = 0] + [n = 26] + 14·[n = 31]` calls on every input
(`sampler_length`, stated for EVERY row n, malformed messages included), summed
over 33 rows to 115 (`budget_sum`, `transcript_length`), and
`verifier_length : … ≤ 115 + B` for a terminal decision reading at most B.
`OraclePortExperiment.{Budget, verifier_budget, first_reads}` (with B = 1,046)
give `≤ 1,161` and `firstReads ≤ Q + 1,161`.

The 40-row analogue reuses R1's per-row theorem `OracleDecisionPrereqSampler.row_length`
through the delegation lemma `AspisRows40.Protocol.chain_eq` (the 40-row
protocol's chains are R1's chains), and sums over 40 rows: 115 + 7·3 = 136.
R1's `VerifierCallBudget.firstReads_le_length` lives in a two-transaction
module (R1VerifierCallBudget) and is re-proved here. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CallBudget
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open OracleDecisionPrereqSampler (rowBudget)

/-- Row n of the 40-row protocol issues at most `rowBudget n` digest calls, on
every input (R1's per-row theorem, through `chain_eq`). -/
theorem row_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat) :
    (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1.length ≤
      rowBudget n := by
  rw [AspisRows40.Protocol.chain_eq]
  exact OracleDecisionPrereqSampler.row_length D H pub pf n

theorem rows_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (ns : List Nat) :
    ((ns.map fun n => (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1).flatten).length ≤
      (ns.map rowBudget).sum := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
    exact Nat.add_le_add (row_length D H pub pf n) ih

/-- 33 × 3 + 1 (initial frame) + 1 (reseed) + 14 (query chain) + 7 × 3 = 136. -/
theorem budget_sum : ((List.range 40).map rowBudget).sum = 136 := by
  decide

theorem budget_split : ((List.range 40).map rowBudget).sum =
    ((List.range 33).map rowBudget).sum + 7 * 3 := by
  decide

/-- The transcript part: the 40 rows issue at most 136 digest calls on every input. -/
theorem transcript_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) :
    (((List.range 40).map fun n =>
      (eval H ((AspisRows40.Protocol.protocol D).chain H pub pf n).toProgram).1).flatten).length ≤ 136 :=
  (rows_length D H pub pf _).trans_eq budget_sum

/-- The sampler-only 40-row verifier (`Starts.verifier`, any Boolean decision). -/
theorem sampler_verifier_length (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) :
    (eval H (AspisRows40.Starts.verifier D d pub pf)).1.length ≤ 136 := by
  unfold AspisRows40.Starts.verifier
  rw [FS2.verifier_eval]
  exact transcript_length D H pub pf

/-- Copy of `OracleDecisionPrereqSampler.verifier_length`: 115 → 136. -/
theorem verifier_length (D : LiteralByteProtocol.Decoder)
    (dO : OracleDecisionFeasibilityCore.Decision) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (B : Nat)
    (hterminal : (eval H (OracleDecisionFeasibilityCore.onBytes dO
      ((AspisRows40.Protocol.protocol D).transcript H pub pf 40) (pf 40))).1.length ≤ B) :
    (eval H (AspisRec40.Decision.verifier D dO pub pf)).1.length ≤ 136 + B := by
  rw [AspisRec40.Decision.verifier_eval, List.length_append]
  exact Nat.add_le_add (transcript_length D H pub pf) hterminal

/-- Copy of `OraclePortExperiment.Budget` with the bound a parameter (R1: 1,046). -/
def Budget (dO : OracleDecisionFeasibilityCore.Decision) (B : Nat) : Prop :=
  ∀ (H : Bytes → State) p m, (eval H (dO p m)).1.length ≤ B

/-- Copy of `OraclePortExperiment.verifier_budget`: R1's 1,161 = 115 + 1,046
becomes 136 + B. -/
theorem verifier_budget (D : LiteralByteProtocol.Decoder)
    (dO : OracleDecisionFeasibilityCore.Decision) (B : Nat) (hB : Budget dO B)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) :
    (eval H (AspisRec40.Decision.verifier D dO pub pf)).1.length ≤ 136 + B :=
  verifier_length D dO H pub pf B (hB H _ _)

/-- Re-proof of R1's `VerifierCallBudget.firstReads_le_length` (generic). -/
theorem firstReads_le_length {I A : Type} [DecidableEq I]
    (t : Table I A) (tr : List (I × A)) : FS.firstReads t tr ≤ tr.length := by
  induction tr generalizing t with
  | nil => simp [FS.firstReads]
  | cons q rest ih =>
    rcases q with ⟨i, a⟩
    have h := ih (put t i a)
    simp only [FS.firstReads, List.length_cons]
    split <;> omega

/-- Copy of `OracleDecisionFeasibilityCompiler.firstReads_eq` for the 40-row
verifier: the compiler's second verifier run adds no distinct calls. -/
theorem firstReads_eq (D : LiteralByteProtocol.Decoder)
    (d : OracleDecisionFeasibilityCore.Decision)
    (buildWords : RawCutProverCompiler.RunView → CanonicalCutEnrichedTranscript.Words)
    (P : RawCutProverCompiler.Prover) (H : Bytes → State) :
    firstReads emptyTable
        (eval H (AspisRec40.Decision.annotated D d buildWords P)).1 =
      firstReads emptyTable (eval H (RawCutProverCompiler.experiment P
        (AspisRec40.Decision.verifier D d))).1 := by
  rw [AspisRec40.Decision.annotated, AspisRec40.Decision.compiled_experiment_eval]
  rw [RawCutProverCompiler.experiment_eval]
  exact OracleProgramRecording.firstReads_repeat_suffix _ _

/-- Copy of `OraclePortExperiment.first_reads`: `Q + 1161` becomes `Q + (136 + B)`. -/
theorem first_reads (D : LiteralByteProtocol.Decoder)
    (dO : OracleDecisionFeasibilityCore.Decision) (B : Nat) (hB : Budget dO B)
    (P : RawCutProverCompiler.Prover) (Q : Nat)
    (hq : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (AspisRec40.Decision.recorded D dO P)).1 ≤ Q + (136 + B) := by
  rw [AspisRec40.Decision.recorded, firstReads_eq]
  rw [RawCutProverCompiler.experiment_eval]
  have hp := hq H
  have hv := verifier_budget D dO B hB H (eval H P).2.1 (eval H P).2.2
  have hr := firstReads_le_length emptyTable
    ((eval H P).1 ++ (eval H (AspisRec40.Decision.verifier D dO (eval H P).2.1 (eval H P).2.2)).1)
  rw [List.length_append] at hr
  exact hr.trans (Nat.add_le_add hp hv)

/-! ## The full 40-row experiment with a parameter decision -/

theorem verifier_enrich (D : LiteralByteProtocol.Decoder) (d : Decision)
    (w : CanonicalCutEnrichedTranscript.Words) (i : Input) :
    AspisRec40.HitMass.verifier D d (enrich w i) = AspisRec40.HitMass.verifier D d i :=
  AspisRec40.Decision.verifier_eq D (d i.stored) w i.statement i.proof

/-- The full experiment's trace: the prover, one verifier run, the same run again. -/
theorem projected_trace_eq (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (H : Bytes → State) :
    (eval H (AspisRec40.HitMass.projected D d P)).1 =
      ((eval H (canon P)).1 ++
        (eval H (AspisRec40.HitMass.verifier D d (eval H (canon P)).2)).1) ++
        (eval H (AspisRec40.HitMass.verifier D d (eval H (canon P)).2)).1 := by
  simp only [AspisRec40.HitMass.projected, AspisRec40.HitMass.annotated,
    AspisRec40.HitMass.recorded, eval_bind, eval, List.append_nil]
  rw [AspisRec40.HitMass.original_eval, AspisRec40.HitMass.compiled_eval]
  dsimp only
  rw [verifier_enrich, AspisRec40.HitMass.original_eval]

/-- Distinct reads of the full 40-row experiment, for every terminal decision
whose every stored instance reads at most B: at most `Q + (136 + B)` (R1's
`Q + 1161` with 115 + 1,046). -/
theorem projected_first_reads (D : LiteralByteProtocol.Decoder) (d : Decision) (B : Nat)
    (hB : ∀ s, Budget (d s) B) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) (H : Bytes → State) :
    firstReads emptyTable (eval H (AspisRec40.HitMass.projected D d P)).1 ≤ Q + (136 + B) := by
  rw [projected_trace_eq, OracleProgramRecording.firstReads_repeat_suffix]
  have hr := firstReads_le_length emptyTable ((eval H (canon P)).1 ++
    (eval H (AspisRec40.HitMass.verifier D d (eval H (canon P)).2)).1)
  rw [List.length_append] at hr
  have hp : (eval H (canon P)).1.length ≤ Q := by rw [canon_eval]; exact hq H
  have hv : (eval H (AspisRec40.HitMass.verifier D d (eval H (canon P)).2)).1.length ≤ 136 + B :=
    verifier_budget D _ B (hB _) H _ _
  exact hr.trans (Nat.add_le_add hp hv)

#print axioms row_length
#print axioms budget_sum
#print axioms budget_split
#print axioms transcript_length
#print axioms sampler_verifier_length
#print axioms verifier_length
#print axioms verifier_budget
#print axioms firstReads_le_length
#print axioms firstReads_eq
#print axioms first_reads
#print axioms verifier_enrich
#print axioms projected_trace_eq
#print axioms projected_first_reads

end AspisRec40.CallBudget
end
