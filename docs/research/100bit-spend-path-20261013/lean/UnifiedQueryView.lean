import R1UnifiedQueryRun
import R1UnifiedRecordCompletion
import R1UnifiedQueryDecoder

/-! The decoded query row represents the actual 31-round prefix, payload,
and query challenge when the table supplies its known oracle values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryView

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView AspisR1.QueryStateList

variable {M Cv W : Type} {L : Nat}

theorem actual_output (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (T : Table (Addr L) State)
    (hT : ∀ b v, T b = some v → v = H b) :
    UnifiedQueryDecoder.output p pub T
      ⟨c1, UnifiedRecords.records p hD H pub c1 payload 31, payload 31⟩
      (states (QuerySampler.state p H
        (H (UnifiedQueryRun.queryAddress p hD H pub c1 payload))) 8)
      ((PrefixAnswers.missing p T
          (UnifiedRecords.records p hD H pub c1 payload 31)).map H ++
        blocks p H (QuerySampler.state p H
          (H (UnifiedQueryRun.queryAddress p hD H pub c1 payload))) 8) =
    (UnifiedRun.transcript p hD H pub c1 payload 31,
      UnifiedRun.message c1 payload 31,
      UnifiedRun.challenge p hD H pub c1 payload 31) := by
  let ctx : UnifiedSemanticContext.Context M :=
    ⟨c1, UnifiedRecords.records p hD H pub c1 payload 31, payload 31⟩
  let s := QuerySampler.state p H
    (H (UnifiedQueryRun.queryAddress p hD H pub c1 payload))
  have hrounds :
      UnifiedSemanticLaw.mkPrefix p pub T ctx
        ((PrefixAnswers.missing p T ctx.records).map H) =
        UnifiedRun.transcript p hD H pub c1 payload 31 := by
    have hrecords := PrefixAnswers.fromAnswers_map p T 0 ctx.records H hT
    have hcompleted := UnifiedRecordCompletion.completed_eq_transcript p hD H pub c1 payload
      hl he 31 (by decide)
    have hprefix :
        TranscriptView.ordinary c1
          (completeRounds p emptyTable H 0 ctx.records) =
        (UnifiedRun.transcript p hD H pub c1 payload 31).rounds := by
      simpa [ctx] using hcompleted
    have hstatement := UnifiedRun.transcript_statement p hD H pub c1 payload 31
    unfold UnifiedSemanticLaw.mkPrefix
    simp only [hrecords]
    cases hrun : UnifiedRun.transcript p hD H pub c1 payload 31 with
    | mk statement rounds =>
      simp only [hrun] at hstatement hprefix ⊢
      cases hstatement
      simpa [ctx] using hprefix
  have hscan :
      Q22.scanOut 8 Q22.q0 (blocks p H s 8) (states s 8).tail
        ((states s 8).headD default) = QueryFirstRead.result p H s := by
    rw [states_tail, states_head]
    rfl
  have hchallenge :
      UnifiedRun.challenge p hD H pub c1 payload 31 =
        UnifiedSampler.liftQuery (QueryFirstRead.result p H s) := by
    simpa [s, UnifiedQueryRun.queryResult] using
      UnifiedQueryRun.query_challenge p hD H pub c1 payload
  change UnifiedQueryDecoder.output p pub T ctx (states s 8)
      ((PrefixAnswers.missing p T ctx.records).map H ++ blocks p H s 8) = _
  rw [UnifiedQueryDecoder.output_append p pub T ctx (states s 8)
    ((PrefixAnswers.missing p T ctx.records).map H) (blocks p H s 8) (by simp)]
  change
    (UnifiedSemanticLaw.mkPrefix p pub T ctx
        ((PrefixAnswers.missing p T ctx.records).map H),
      Message.payload (payload 31),
      UnifiedSampler.liftQuery
        (Q22.scanOut 8 Q22.q0 (blocks p H s 8) (states s 8).tail
          ((states s 8).headD default))) = _
  rw [hrounds, hscan]
  rw [show UnifiedRun.message c1 payload 31 = Message.payload (payload 31) by rfl]
  rw [← hchallenge]

theorem firstCell_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (c1, payload) 31) =
      some (UnifiedSteps.address p hD H pub c1 payload 31) := by
  rw [UnifiedProtocol.chain_eq p hD extract H pub (c1, payload) 31]
  change firstCell (UnifiedSampler.samp p hD 31
    (UnifiedRun.transcript p hD H pub c1 payload 31) (.payload (payload 31))) = _
  rw [UnifiedSampler.row_query]
  rw [UnifiedSteps.payload_address p hD H pub c1 payload 31 (by decide)]
  rfl

#print axioms actual_output
#print axioms firstCell_eq

end AspisR1.UnifiedQueryView
end
