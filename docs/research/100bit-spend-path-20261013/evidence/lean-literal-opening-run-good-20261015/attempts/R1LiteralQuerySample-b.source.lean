import R1LiteralByteSampler
import R1LiteralQueryRead
import R1QuerySamplerBridge
import AspisV8R19.Q22SamplerInvariants

/-! A successful literal row-31 query result is accepted by the strict
positional query reader. This is sampler-result validity only; it makes no
probability, source-refinement, acceptance, or security claim. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQuerySample

open FS FS2 FS2.Duplex
open R0C.V3
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisV8R19.Q22SamplerInvariants
open AspisV8R19.R412LegalQueryEnumeration
open AspisR1.QueryFirstRead AspisR1.QuerySampler AspisR1.QueryStateList
open AspisR1.QuerySamplerBridge
open AspisR1.TranscriptView

/-- Every finite `scanOut` execution preserves the old scanner invariant.
The only input fact used is the existing bound on each decoded sampler word. -/
theorem scanOut_result_valid :
    ∀ (n : Nat) (q : AspisV8R19.Q22WordScan.ScanState)
      (bs xs : List State) (s : State),
      Valid q → ResultValid (R0C.V3.Q22.scanOut n q bs xs s).1 := by
  intro n
  induction n with
  | zero =>
      intro q bs xs s hq
      simpa [R0C.V3.Q22.scanOut] using finish_valid q hq
  | succ n ih =>
      intro q bs xs s hq
      cases bs with
      | nil =>
          simpa [R0C.V3.Q22.scanOut] using finish_valid q hq
      | cons b bs =>
          cases xs with
          | nil =>
              simpa [R0C.V3.Q22.scanOut] using finish_valid q hq
          | cons x xs =>
              by_cases hd : q.draws < 64
              · let r := AspisV8R19.Q22WordScan.scan q
                  (AspisV8R19.SamplerWords.words 18 b)
                have hr : Valid r.1 := by
                  apply scan_valid q _ hq
                  intro y hy
                  exact AspisV8R19.SamplerWords.words_bounded 18 b y hy
                cases hs : r.2 with
                | false =>
                    simpa [R0C.V3.Q22.scanOut, hd, r, hs] using
                      ih r.1 bs xs x hr
                | true =>
                    simpa [R0C.V3.Q22.scanOut, hd, r, hs] using
                      finish_valid r.1 hr
              · simpa [R0C.V3.Q22.scanOut, hd] using finish_valid q hq

theorem valid_row31_success_decodes
    (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (xs : List Nat) (state : State)
    (hm : LiteralTranscript.valid 31 m)
    (hout : (eval H (LiteralByteSampler.samp 31 P m).toProgram).2 =
      (Value.queries (.ok xs), state)) :
    ∃ q, LiteralQueryRead.decode xs = some q := by
  cases m with
  | initial root word => simp [LiteralTranscript.valid] at hm
  | c2 bytes word => simp [LiteralTranscript.valid] at hm
  | second bytes word => simp [LiteralTranscript.valid] at hm
  | payload bytes =>
      let p := SelectedTranscriptParams.params
      let P' := LiteralTranscript.erasePrefix P
      let msg : SelectedTranscriptParams.Message := bytes
      let addr := UnifiedSampler.absorb p 31 P' msg
      let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State :=
        fun a => H a.toBytes
      let qrun := QueryFirstRead.result p H'
        (QuerySampler.state p H' (H' addr))
      have hD : 5 ≤ p.D := by
        norm_num [p, SelectedTranscriptParams.params, SelectedTranscriptParams.D]
      have hrow : UnifiedSampler.samp p hD 31 P' (.payload msg) =
          QuerySamplerBridge.sampler p addr UnifiedSampler.liftQuery :=
        UnifiedSampler.row_query p hD P' msg
      have hselected :
          (eval H' (LiteralTranscript.samp 31 P (.payload bytes)).toProgram).2 =
            UnifiedSampler.liftQuery qrun := by
        change (eval H' (UnifiedSampler.samp p hD 31 P' (.payload msg)).toProgram).2 = _
        rw [hrow]
        exact QuerySamplerBridge.output p H' addr UnifiedSampler.liftQuery
      have hmap := congrArg Prod.snd
        (LiteralByteSampler.eval_eq H 31 P (.payload bytes))
      have hresult :
          (eval H (LiteralByteSampler.samp 31 P (.payload bytes)).toProgram).2 =
            UnifiedSampler.liftQuery qrun := by
        calc
          _ = (AspisV8R19.OracleProgramOps.mapView FS2.Duplex.Addr.toBytes
                (eval H' (LiteralTranscript.samp 31 P (.payload bytes)).toProgram)).2 := hmap
          _ = UnifiedSampler.liftQuery qrun := by
                simp [AspisV8R19.OracleProgramOps.mapView, hselected]
      have hrun : UnifiedSampler.liftQuery qrun = (Value.queries (.ok xs), state) :=
        hresult.symm.trans hout
      have hxs : qrun.1 = .ok xs := by
        have h := congrArg Prod.fst hrun
        simpa [UnifiedSampler.liftQuery] using h
      have hvalidRun : ResultValid qrun.1 := by
        change ResultValid
          (R0C.V3.Q22.scanOut 8 Q22.q0
            (QueryStateList.blocks p H' (QuerySampler.state p H' (H' addr)) 8)
            (QueryStateList.advances (QuerySampler.state p H' (H' addr)) 8)
            (QuerySampler.state p H' (H' addr) 0)).1
        apply scanOut_result_valid
        simp [Valid, Q22.q0]
      have hvalidXs : ResultValid (.ok xs) := by
        rw [← hxs]
        exact hvalidRun
      have hshape : xs.Nodup ∧ xs.length = 22 ∧ ∀ x ∈ xs, x < 262144 := by
        simpa [ResultValid] using hvalidXs
      refine ⟨(legalOfList xs hshape.1 hshape.2.1 hshape.2.2).val, ?_⟩
      unfold LiteralQueryRead.decode
      rw [dif_pos hshape]

#print axioms scanOut_result_valid
#print axioms valid_row31_success_decodes

end AspisR1.LiteralQuerySample
end
