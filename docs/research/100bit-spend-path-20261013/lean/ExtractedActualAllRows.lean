import ExtractedFirstPairedReachability
import ExtractedCircleCalls
import ExtractedOpeningRun
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.ActualAllRows
open r1_wire BeginCalls

def allRows (opening : List U8) : List U8 :=
  ActualFull25.rows ++ [25#u8,26#u8] ++ opening

def Complete (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (Q : QueriesModel.Boundaries) (D : aspis_core.Digest32 Unit)
    (pre : Prefix) (initial : SemanticTranscript Unit) (sem : r1_semantic.Verified Unit)
    (view : verifier.View) (prepared : verifier.Prepared) : Prop :=
  ∃ (t25 t26 t27 : SemanticTranscript Unit) (r25 r26 : ValidatedRecord)
    (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (start last : transcript.Transcript Unit) (seed : Array U8 32#usize) (opening : List U8),
    SemanticRun D pre ActualFull25.rows initial t25
      (challengeList sem.challenges ++ sem.alpha.val) ∧
    sem.state_before_z0 = t25.state ∧
    Prefix.validated_record pre 25#u8 = ok (.Ok r25) ∧
    pre.records.val[25]? = some r25.framed ∧
    FinishModel.circle_validated B D t25 r25 = ok (.Ok z0,t26) ∧
    Prefix.validated_record pre 26#u8 = ok (.Ok r26) ∧
    pre.records.val[26]? = some r26.framed ∧
    FinishModel.circle_validated B D t26 r26 = ok (.Ok z1,t27) ∧
    sem.transcript = t27 ∧ t27.next_row.val = 27 ∧
    D.digest () (CallerStep.reseedParts t27.state view.variant) = ok seed ∧
    start = {state := seed,hash := ()} ∧
    OpeningRun.Run Q D start opening last ∧ prepared.state = last.state ∧
    last.hash = start.hash ∧
    ((transport.Variant.folds view.variant = ok 1#usize ∧
        (allRows opening).map (fun row => row.val) = List.range 32) ∨
     (transport.Variant.folds view.variant = ok 2#usize ∧
        (allRows opening).map (fun row => row.val) = List.range 33))

/-- One actual accepted first caller reaches every source row, including the
row26-to-opening reseed and final prepared state. The two-fold schedule has33
rows; S1 has32. No child-success, run or byte-equality premise is supplied.
All displayed arithmetic/decoder/custody interpretation parameters remain explicit. -/
theorem first_all_rows {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries) (Q : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T (OpeningRun.bindQueries P Q) (FinishModel.finish R B) D)
      mark error asf8 proof k = ok (.Ok out)) :
    ∃ s supplied view sem prepared pre initial,
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧ supplied = PreparationBinding.preparationPublic s ∧
      T.view proof = ok (.Ok view) ∧
      PrefixAdapter.parseAccepted view.semantic = ok (.Ok pre) ∧
      r1_semantic.public_transcript D supplied () pre.c1_root = ok (.Ok initial) ∧
      Complete R B Q D pre initial sem view prepared := by
  obtain ⟨s,supplied,view,sem,prepared,pre,initial,afterBegin,challenges,
    hd,heq,hview,hparse,hpublic,hbegin,hfinish,hprepare⟩ :=
    FirstPaired.first_paired invalidAccountData T (OpeningRun.bindQueries P Q) R B D
      mark error asf8 proof k out h
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,
    hrounds,hch,hstate,htranscript,hclaims,hr25,hd25,hz0,hr26,hd26,hz1,hz⟩ :=
    FinishCalls.finish_success R B D supplied pre afterBegin challenges
      (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) sem hfinish
  obtain ⟨qb,hb,eqb⟩ := begin_success D pre initial afterBegin challenges hbegin
  obtain ⟨qr,hr,eqr⟩ := RoundCalls.rounds_success R D pre afterBegin t25 running sem.alpha hrounds
  have run : SemanticRun D pre ActualFull25.rows initial t25
      (challengeList sem.challenges ++ sem.alpha.val) := by
    rw [hch,← eqb,← eqr]
    exact ActualFull25.append_run D pre hb hr
  obtain ⟨hrow25,hbytes25⟩ := CircleCalls.circle25_record_bytes pre r25 hr25
  obtain ⟨hrow26,hbytes26⟩ := CircleCalls.circle26_record_bytes pre r26 hr26
  obtain ⟨_,block26,tag26,next26,abs26,state26,_,hn26,_,_,_,_,he26⟩ :=
    CircleCalls.circle26_step B D t26 t27 r26 z1 hrow26 hz1
  have hnext27 : t27.next_row.val = 27 := by rw [he26]; exact hn26
  obtain ⟨start,last,hseed,hprepared,tail⟩ := OpeningRun.prepare_run P Q D sem view () prepared hprepare
  obtain ⟨seed,hseedDigest,hstart⟩ := CallerStep.opening_new_success D () sem.transcript.state view.variant start hseed
  have hseed27 : D.digest () (CallerStep.reseedParts t27.state view.variant) = ok seed := by
    simpa only [htranscript] using hseedDigest
  refine ⟨s,supplied,view,sem,prepared,pre,initial,hd,heq,hview,hparse,hpublic,?_⟩
  rcases tail with ⟨hfolds,hRun⟩ | ⟨hfolds,hRun⟩
  · refine ⟨t25,t26,t27,r25,r26,z0,z1,start,last,seed,
      [27#u8,28#u8,29#u8,30#u8,31#u8],run,hstate,hr25,hbytes25,hz0,hr26,hbytes26,hz1,
      htranscript,hnext27,hseed27,hstart,hRun,hprepared,hRun.hash,Or.inl ⟨hfolds,?_⟩⟩
    rfl
  · refine ⟨t25,t26,t27,r25,r26,z0,z1,start,last,seed,
      [27#u8,28#u8,29#u8,30#u8,31#u8,32#u8],run,hstate,hr25,hbytes25,hz0,hr26,hbytes26,hz1,
      htranscript,hnext27,hseed27,hstart,hRun,hprepared,hRun.hash,Or.inr ⟨hfolds,?_⟩⟩
    rfl
#print axioms first_all_rows
end AspisR1PublicPreparation.ActualAllRows
