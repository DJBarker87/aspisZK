import OracleDecisionPrereqPaths

/-! Exact call count on constructor-valid schedules. No success assumption
for Merkle comparisons; the constructed decision executes every path. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionPrereqExact
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open BinHonestStartFrames
open OracleDecisionPrereqSampler

def Shape : Nat → TranscriptView.Message SelectedTranscriptParams.Message → Prop
  | 0, .initial _ => True
  | _+1, .payload _ => True
  | _, _ => False

theorem sampler_exact (H : Addr L → State) (n : Nat)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message) (hv : Shape n m) :
    (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      n P m).toProgram).1.length = rowBudget n := by
  cases n with
  | zero =>
    cases m with
    | initial root =>
      rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
      simp [rowBudget]
    | payload msg => cases hv
  | succ n =>
    cases m with
    | initial root => cases hv
    | payload msg =>
      by_cases h26 : n+1 = 26
      · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
        simp [rowBudget]
      · by_cases h31 : n+1 = 31
        · rw [h31, UnifiedSampler.row_query]
          change (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1.length + 1 = _
          rw [R19BudgetSamplerReads.query_tail_length]
          norm_num [rowBudget]
        · rw [UnifiedSampler.row_ordinary p _ (n+1) (by omega) h26 h31,
            DuplexSamplers.plain_eval]
          simp [rowBudget, h26, h31]

theorem row_exact (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat)
    (hv : Shape n (LiteralTranscript.erase (pf n))) :
    (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1.length = rowBudget n := by
  change (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1.length = _
  rw [LiteralByteSampler.eval_eq]
  change ((eval (fun a => H a.toBytes) (LiteralTranscript.samp n _ (pf n)).toProgram).1.map _).length = _
  rw [List.length_map]
  exact sampler_exact _ _ _ _ hv

theorem rows_exact (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (ns : List Nat)
    (hv : ∀ n ∈ ns, Shape n (LiteralTranscript.erase (pf n))) :
    ((ns.map fun n => (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1).flatten).length =
      (ns.map rowBudget).sum := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
    rw [row_exact D H pub pf n (hv n (by simp)), ih (fun i hi => hv i (by simp [hi]))]

theorem verifier_exact (D : LiteralByteProtocol.Decoder)
    (os : List OracleDecisionPrereqPaths.Opening) (frames : List Bytes)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (q d : Nat) (hc : os.length = 3*q) (hd : ∀ o ∈ os, o.slots.length = d)
    (hv : ∀ n < 33, Shape n (LiteralTranscript.erase (pf n))) :
    (eval H (OracleDecisionFeasibilityCore.verifier D
      (OracleDecisionPrereqPaths.decision os frames) pub pf)).1.length =
        OracleDecisionPrereqPaths.B_V q d frames.length := by
  rw [OracleDecisionFeasibilityBudget.verifier_eval, List.length_append,
    rows_exact D H pub pf (List.range 33) (by simpa only [List.mem_range] using hv), budget_sum]
  change 115 + (eval H (OracleDecisionPrereqPaths.terminal os frames)).1.length = _
  rw [OracleDecisionPrereqPaths.terminal_length,
    OracleDecisionPrereqPaths.pathCalls_uniform os d hd, hc]
  unfold OracleDecisionPrereqPaths.B_V
  omega

#print axioms sampler_exact
#print axioms row_exact
#print axioms rows_exact
#print axioms verifier_exact
end AspisR1.OracleDecisionPrereqExact
end
