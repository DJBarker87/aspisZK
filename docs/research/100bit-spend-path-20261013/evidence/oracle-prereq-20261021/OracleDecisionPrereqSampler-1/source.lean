import OracleDecisionFeasibilityBudget

/-! Tight issued-call allowance, including malformed messages. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqSampler
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open BinHonestStartFrames

def rowBudget (n : Nat) : Nat :=
  3 + (if n = 0 then 1 else 0) + (if n = 26 then 1 else 0) +
    (if n = 31 then 14 else 0)

theorem sampler_length (H : Addr L → State) (n : Nat)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message) :
    (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      n P m).toProgram).1.length ≤ rowBudget n := by
  cases n with
  | zero =>
    cases m with
    | initial root =>
      rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
      simp [rowBudget]
    | payload msg =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval, rowBudget]
  | succ n =>
    cases m with
    | initial root =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval, rowBudget]
    | payload msg =>
      by_cases h26 : n+1 = 26
      · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
        simp [rowBudget]
      · by_cases h31 : n+1 = 31
        · rw [h31, UnifiedSampler.row_query]
          change (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1.length + 1 ≤ _
          rw [R19BudgetSamplerReads.query_tail_length]
          norm_num [rowBudget]
        · rw [UnifiedSampler.row_ordinary p _ (n+1) (by omega) h26 h31,
            DuplexSamplers.plain_eval]
          simp [rowBudget, h26, h31]

theorem row_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat) :
    (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1.length ≤
      rowBudget n := by
  change (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1.length ≤ _
  rw [LiteralByteSampler.eval_eq]
  change ((eval (fun a => H a.toBytes) (LiteralTranscript.samp n _ (pf n)).toProgram).1.map _).length ≤ _
  rw [List.length_map]
  exact sampler_length _ _ _ _

theorem rows_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (ns : List Nat) :
    ((ns.map fun n => (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1).flatten).length ≤
      (ns.map rowBudget).sum := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
    exact Nat.add_le_add (row_length D H pub pf n) ih

theorem budget_sum : ((List.range 33).map rowBudget).sum = 115 := by
  decide

theorem transcript_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) :
    (((List.range 33).map fun n =>
      (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1).flatten).length ≤ 115 := by
  exact (rows_length D H pub pf _).trans_eq budget_sum

theorem verifier_length (D : LiteralByteProtocol.Decoder)
    (dO : OracleDecisionFeasibilityCore.Decision) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (B : Nat)
    (hterminal : (eval H (OracleDecisionFeasibilityCore.onBytes dO
      ((LiteralByteProtocol.protocol D).transcript H pub pf 33) (pf 33))).1.length ≤ B) :
    (eval H (OracleDecisionFeasibilityCore.verifier D dO pub pf)).1.length ≤ 115 + B := by
  rw [OracleDecisionFeasibilityBudget.verifier_eval, List.length_append]
  exact Nat.add_le_add (transcript_length D H pub pf) hterminal

#print axioms sampler_length
#print axioms row_length
#print axioms rows_length
#print axioms budget_sum
#print axioms transcript_length
#print axioms verifier_length
end AspisR1.OracleDecisionPrereqSampler
end
