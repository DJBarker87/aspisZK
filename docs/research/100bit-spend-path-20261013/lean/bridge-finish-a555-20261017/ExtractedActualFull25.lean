import ExtractedVerifyFinishReachability
import ExtractedSemanticRoundsReachability
import ExtractedSourceFull25Typed
import ExtractedFirstHelperBinding
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.ActualFull25
open r1_wire BeginCalls

theorem append_run {H : Type} (D : aspis_core.Digest32 H) (pre : Prefix)
    {rows first mid qs tail after rt}
    (left : SemanticRun D pre rows first mid qs)
    (right : SemanticRun D pre tail mid after rt) :
    SemanticRun D pre (rows ++ tail) first after (qs ++ rt) := by
  induction left with
  | nil => exact right
  | cons hr hs _ ih => exact SemanticRun.cons hr hs (ih right)

def rows : List U8 := BeginCalls.rows ++ RoundCalls.rows

theorem rows_schedule : rows.map (fun row => row.val) = List.range 25 := by rfl

/-- Composition of the actual begin and complete finish bodies. The resulting
source run's values are exactly the returned challenges and alpha. -/
theorem begin_finish_run (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : Prefix)
    (initial afterBegin : SemanticTranscript H) (challenges : Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (out : r1_semantic.Verified H)
    (hb : begin D pre initial = ok (.Ok challenges,afterBegin))
    (hf : FinishModel.finish R B D pub pre afterBegin challenges obs = ok (.Ok out)) :
    ∃ t25, SemanticRun D pre rows initial t25
      (challengeList out.challenges ++ out.alpha.val) ∧ out.state_before_z0 = t25.state := by
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,hr,hch,hstate,_⟩ :=
    FinishCalls.finish_success R B D pub pre afterBegin challenges obs out hf
  obtain ⟨qb,hbegin,eqb⟩ := begin_success D pre initial afterBegin challenges hb
  obtain ⟨qr,hrounds,eqr⟩ := RoundCalls.rounds_success R D pre afterBegin t25 running out.alpha hr
  refine ⟨t25,?_,hstate⟩
  rw [hch,← eqb,← eqr]
  exact append_run D pre hbegin hrounds

/-- Actual first acceptance constructs the 25 complete source frames. The
strict parser identifies the same bytes and their typed values; no hbytes,
child-success, decoded-public or selected-message witness is assumed. Digest,
arithmetic and allocation interpretations remain the displayed parameters. -/
theorem first_full25 {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k =
        ok (.Ok out)) :
    ∃ s supplied view, ∃ (sem : r1_semantic.Verified Unit) (pre : Prefix)
      (initial t25 : SemanticTranscript Unit),
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧ supplied = PreparationBinding.preparationPublic s ∧
      T.view proof = ok (.Ok view) ∧
      PrefixAdapter.parseAccepted view.semantic = ok (.Ok pre) ∧
      r1_semantic.public_transcript D supplied () pre.c1_root = ok (.Ok initial) ∧
      sem.state_before_z0 = t25.state ∧
      ∃ cs : List (SourceFull25.Call D pre), ∃ values : AspisR1.SemanticPrefixCodec.Full,
        SourceFull25.Trace D pre initial t25 cs ∧ cs.map SourceFull25.Call.row = rows ∧
        cs.map SourceFull25.Call.q = challengeList sem.challenges ++ sem.alpha.val ∧
        SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre ∧
        AspisR1.SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames cs) =
          some (AspisR1.SemanticPrefixCodec.entriesOf values) ∧
        (∀ c ∈ cs, (c.record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte).length ≤ 901) := by
  obtain ⟨s,supplied,view,sem,pre,initial,afterBegin,challenges,bytes,wire,
    hd,heq,hv,hp,hh,hb,hf,hs,hw,hparse,hn⟩ :=
    FirstHelperBinding.first_helper_parsePublic invalidAccountData T P
      (FinishModel.finish R B) D mark error asf8 proof k out h
  obtain ⟨t25,run,hstate⟩ := begin_finish_run R B D supplied pre initial afterBegin challenges
    (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) sem hb hf
  obtain ⟨cs,values,ht,hr,hq,hbytes,hdecode,hbound⟩ :=
    SourceFull25.run_typedFull D view.semantic pre hp run rows_schedule
  exact ⟨s,supplied,view,sem,pre,initial,t25,hd,heq,hv,hp,hh,hstate,
    cs,values,ht,hr,hq,hbytes,hdecode,hbound⟩

#print axioms append_run
#print axioms rows_schedule
#print axioms begin_finish_run
#print axioms first_full25
end AspisR1PublicPreparation.ActualFull25
