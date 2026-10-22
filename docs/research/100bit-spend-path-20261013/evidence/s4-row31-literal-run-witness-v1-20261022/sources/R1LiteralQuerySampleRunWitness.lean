import R1LiteralQuerySample

set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQuerySampleRunWitness

open FS FS2 FS2.Duplex
open R0C.V3
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisV8R19.Q22SamplerInvariants
open AspisV8R19.R412LegalQueryEnumeration
open AspisR1.QueryFirstRead AspisR1.QuerySampler AspisR1.QueryStateList
open AspisR1.QuerySamplerBridge
open AspisR1.TranscriptView AspisR1.LiteralQuerySample

/-- The exact list-valued scan used by a successful literal row-31 payload
    sampler, before the strict reader turns it into `Fin 22` coordinates. -/
def row31PayloadQueryRun (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (bytes : SelectedTranscriptParams.Message) :=
  let p := SelectedTranscriptParams.params
  let P' := LiteralTranscript.erasePrefix P
  let addr := UnifiedSampler.absorb p 31 P' bytes
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State :=
    fun a => H a.toBytes
  QueryFirstRead.result p H' (QuerySampler.state p H' (H' addr))

theorem valid_row31_success_decodes_with_run
    (H : Bytes → State) (P : LiteralTranscript.Prefix)
    (bytes : SelectedTranscriptParams.Message) (xs : List Nat) (state : State)
    (hout : (eval H (LiteralByteSampler.samp 31 P (.payload bytes)).toProgram).2 =
      (Value.queries (.ok xs), state)) :
    ∃ q, LiteralQueryRead.decode xs = some q ∧
      (row31PayloadQueryRun H P bytes).1 = .ok xs := by
  let p := SelectedTranscriptParams.params
  let P' := LiteralTranscript.erasePrefix P
  let msg := bytes
  let addr := UnifiedSampler.absorb p 31 P' msg
  let H' : FS2.Duplex.Addr SelectedTranscriptParams.L → State :=
    fun a => H a.toBytes
  let qrun := row31PayloadQueryRun H P bytes
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
  refine ⟨(legalOfList xs hshape.1 hshape.2.1 hshape.2.2).val, ?_, ?_⟩
  unfold LiteralQueryRead.decode
  rw [dif_pos hshape]
  exact hxs

#print axioms valid_row31_success_decodes_with_run

end AspisR1.LiteralQuerySampleRunWitness
end
