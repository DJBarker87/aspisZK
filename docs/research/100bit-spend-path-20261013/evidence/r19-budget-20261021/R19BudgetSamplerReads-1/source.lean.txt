import BinHonestQueryBudget

/-! Issued-query accounting for the literal Lean sampler, uniform in oracle,
message validity and decoder results. No source-trace refinement is used. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R19BudgetSamplerReads
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open BinHonestStartFrames

theorem query_tail_length {C : Type} (H : Addr L → State)
    (out : List State → List State → C) (n : Nat) (s : State)
    (bs xs : List State) :
    (eval H (QuerySampler.chain p out n s bs xs).toProgram).1.length = 2*n := by
  induction n generalizing s bs xs with
  | zero => rfl
  | succ n ih =>
    simp only [QuerySampler.chain, Sampler.toProgram, eval, List.length_cons]
    rw [ih]
    omega

theorem sampler_length (H : Addr L → State) (n : Nat)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message) :
    (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D])
      n P m).toProgram).1.length ≤ 17 := by
  cases n with
  | zero =>
    cases m with
    | initial root =>
      rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
      simp only [List.length_cons, List.length_nil]
      omega
    | payload msg =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval]
  | succ n =>
    cases m with
    | initial root =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval]
    | payload msg =>
      by_cases h26 : n+1 = 26
      · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
        simp only [List.length_cons, List.length_nil]
        omega
      · by_cases h31 : n+1 = 31
        · rw [h31, UnifiedSampler.row_query]
          change (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1.length + 1 ≤ 17
          rw [query_tail_length]
        · rw [UnifiedSampler.row_ordinary p _ (n+1) (by omega) h26 h31,
            DuplexSamplers.plain_eval]
          simp only [List.length_cons, List.length_nil]
          omega

theorem row_length (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof) (n : Nat) :
    (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1.length ≤ 17 := by
  change (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1.length ≤ 17
  rw [LiteralByteSampler.eval_eq]
  change ((eval (fun a => H a.toBytes) (LiteralTranscript.samp n _ (pf n)).toProgram).1.map _).length ≤ 17
  rw [List.length_map]
  exact sampler_length _ _ _ _

#print axioms query_tail_length
#print axioms sampler_length
#print axioms row_length
end AspisR1.R19BudgetSamplerReads
end
