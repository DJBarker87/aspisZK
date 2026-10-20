import BinHonestStartFrames

set_option autoImplicit false
noncomputable section
namespace AspisR1.BinHonestQueryBudget
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound
open BinHonestStartFrames
abbrev raw (tr : List (Addr L × State)) : List (Bytes × State) :=
  tr.map (fun q => (q.1.toBytes, q.2))

theorem query_tail_zero {C : Type} (H : Addr L → State)
    (out : List State → List State → C) (n : Nat) (s : State)
    (bs xs : List State) (T : Table Bytes State) :
    decoderFirstReads dec T (raw (eval H (QuerySampler.chain p out n s bs xs).toProgram).1) = 0 := by
  induction n generalizing s bs xs T with
  | zero => rfl
  | succ n ih =>
    simp only [QuerySampler.chain, Sampler.toProgram, eval, raw, List.map_cons,
      decoderFirstReads, reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
      and_false, if_false, zero_add]
    exact ih _ _ _ _

theorem sampler_starts (H : Addr L → State) (n : Nat)
    (P : UnifiedSampler.Prefix SelectedTranscriptParams.Message LiteralTranscript.E L)
    (m : TranscriptView.Message SelectedTranscriptParams.Message)
    (T : Table Bytes State) :
    decoderFirstReads dec T (raw (eval H (UnifiedSampler.samp p
      (by norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]) n P m).toProgram).1)
      ≤ 1 + if n = 26 then 1 else 0 := by
  cases n with
  | zero =>
    cases m with
    | initial root =>
      rw [UnifiedSampler.row_zero, DuplexSamplers.initial_eval]
      simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
        reject_row_zero, reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
        and_false, if_false, zero_add]
      split <;> norm_num
    | payload msg =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstReads, reject_squeeze]
  | succ n =>
    cases m with
    | initial root =>
      simp [UnifiedSampler.samp, UnifiedSampler.invalid, Sampler.toProgram, eval,
        raw, decoderFirstReads, reject_squeeze]
    | payload msg =>
      by_cases h26 : n+1 = 26
      · rw [h26, UnifiedSampler.row_reseed, DuplexSamplers.reseeded_eval]
        simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
          reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
          and_false, if_false, zero_add]
        split <;> split <;> norm_num
      · by_cases h31 : n+1 = 31
        · rw [h31, UnifiedSampler.row_query]
          change (if T _ = none ∧ dec _ T ≠ none then 1 else 0) +
            decoderFirstReads dec _ (raw (eval H (QuerySampler.chain p _ 8 _ [] []).toProgram).1) ≤ _
          rw [query_tail_zero]
          split <;> norm_num
        · rw [UnifiedSampler.row_ordinary p _ (n+1) (by omega) h26 h31,
            DuplexSamplers.plain_eval]
          simp only [raw, List.map_cons, List.map_nil, decoderFirstReads,
            reject_squeeze, reject_advance, ne_eq, not_true_eq_false,
            and_false, if_false, zero_add, h26]
          split <;> norm_num

theorem row_starts (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (n : Nat) (T : Table Bytes State) :
    decoderFirstReads dec T
      (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1 ≤
        1 + if n = 26 then 1 else 0 := by
  change decoderFirstReads dec T
    (eval H (LiteralByteSampler.samp n _ (pf n)).toProgram).1 ≤ _
  rw [LiteralByteSampler.eval_eq]
  exact sampler_starts (fun a => H a.toBytes) n _ _ T

theorem rows_bound (D : LiteralByteProtocol.Decoder) (H : Bytes → State)
    (pub : LiteralTranscript.Public) (pf : RawCutProverCompiler.Proof)
    (ns : List Nat) (hn : ns.Nodup) (T : Table Bytes State) :
    decoderFirstReads dec T
      (ns.map (fun n => (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1)).flatten ≤
        ns.length + if 26 ∈ ns then 1 else 0 := by
  induction ns generalizing T with
  | nil => simp [decoderFirstReads]
  | cons n ns ih =>
    rw [List.map_cons, List.flatten_cons, decoderFirstReads_append]
    have hb := row_starts D H pub pf n T
    have ht := ih (List.nodup_cons.mp hn).2 (applyTrace T (eval H ((LiteralByteProtocol.protocol D).chain H pub pf n).toProgram).1)
    have hn' := (List.nodup_cons.mp hn).1
    simp only [List.length_cons, List.mem_cons]
    by_cases he : n = 26
    · subst n
      simp only [if_pos rfl, true_or, if_true] at *
      have hm : 26 ∉ ns := hn'
      simp only [hm, if_false] at ht
      omega
    · by_cases hm : 26 ∈ ns <;> simp_all only [if_false, if_true, eq_comm, false_or] <;> omega

theorem verifier_starts (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (H : Bytes → State) (pub : LiteralTranscript.Public)
    (pf : RawCutProverCompiler.Proof) (T : Table Bytes State) :
    decoderFirstReads dec T (eval H (verifier D d pub pf)).1 ≤ 34 := by
  unfold RawCutProverCompiler.verifier
  rw [FS2.verifier_eval]
  exact (rows_bound D H pub pf (List.range 33) List.nodup_range T).trans (by norm_num)

theorem recorded_starts (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (Q : Nat) (hq : DecoderQueryAccounting.AdversaryQueries P Q)
    (H : Bytes → State) :
    decoderFirstReads dec emptyTable (eval H (recorded D d P)).1 ≤ Q+34 := by
  change decoderFirstReads dec emptyTable
    (eval H (experiment (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P)
      (verifier D d))).1 ≤ Q+34
  rw [RawCutCompilerDecoderStartLaw.decoderStarts_eq dec D d
    (BinCompiledRunWordStability.wordsFromRun D) P H,
    RawCutProverCompiler.experiment_eval, decoderFirstReads_append]
  exact Nat.add_le_add ((DecoderQueryAccounting.starts_le_queries dec _ _).trans (hq H))
    (verifier_starts D d H _ _ _)

#print axioms query_tail_zero
#print axioms sampler_starts
#print axioms row_starts
#print axioms rows_bound
#print axioms verifier_starts
#print axioms recorded_starts
end AspisR1.BinHonestQueryBudget
end
