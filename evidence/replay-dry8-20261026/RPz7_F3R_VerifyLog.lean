import RPz7_F3R_VerifySplit
import RPz7_F3R_BeginTrace
import RPz7_F3R_RoundsTrace
import RPz7_F3R_PublicLog
import RPz7_F3R_TraceAppend
import RPz7_S1SemanticCodeBeginExactV1
import RPz7_S1SemanticCodeRoundsExactV1
import RPz7_PSem_RoundCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_VerifyLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog SourceGlobalOracleInitial

theorem log (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (sem : r1_semantic.Verified Unit)
    (success : erase (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes () none)=ok (.Ok sem)) :
    ∃ (pre : r1_wire.Prefix) (t0 t25 t26 t27 : r1_wire.SemanticTranscript Unit)
      (cs : List (SourceFull25.Call D pre))
      (init : PublicInitCall D pub pre.c1_root t0)
      (r25 r26 : r1_wire.ValidatedRecord) (z0 z1 : aspis_core.circle.SecureCirclePoint),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      r1_semantic.public_transcript D pub () pre.c1_root=ok (.Ok t0) ∧
      SourceFull25.Trace D pre t0 t25 cs ∧ cs.map (fun c=>c.row.val)=List.range 25 ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated B D t25 r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated B D t26 r26=ok (.Ok z1,t27) ∧
      sem.transcript=t27 ∧
      observe (run (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes () none)).1=
        (initPair init::sourceLog cs) ++
        (observe (run (S1SemanticCode.circleValidated B D t25 r25)).1 ++
          observe (run (S1SemanticCode.circleValidated B D t26 r26)).1) := by
  obtain ⟨pre,t0,t15,challenges,parsed,initialized,begin,finish,logs⟩ :=
    F3R_VerifySplit.split R B D pub bytes () sem success
  obtain ⟨running,alpha,t25,r25,z0,t26,r26,z1,t27,rounds,read25,circle25,read26,circle26,transcript,finishLog⟩ :=
    F3R_FinishSplit.split R B D pub pre t15 challenges sem finish
  have rawBegin := (S1SemanticCode.begin_erasure D pre t0).symm.trans begin
  have rawRounds := (S1SemanticCode.rounds_erasure R D pre t15).symm.trans rounds
  obtain ⟨qs0,run0,values0⟩ := BeginCalls.begin_success D pre t0 t15 challenges rawBegin
  obtain ⟨qs1,run1,values1⟩ := PSem_RoundCalls.rounds_success R D pre t15 t25 running alpha rawRounds
  obtain ⟨cs0,trace0,rows0,qs0⟩ := SourceFull25.calls_of_run D pre run0
  obtain ⟨cs1,trace1,rows1,qs1⟩ := SourceFull25.calls_of_run D pre run1
  have order0 : cs0.map (fun c=>c.row.val)=List.range 15 := by
    have h := congrArg (List.map UScalar.val) rows0
    simp only [List.map_map,Function.comp_def] at h
    change cs0.map (fun c=>c.row.val)=BeginCalls.rows.map UScalar.val at h
    exact h.trans (by rfl)
  have order1 : cs1.map (fun c=>c.row.val)=(List.range 10).map (fun j=>15+j) := by
    have h := congrArg (List.map UScalar.val) rows1
    simp only [List.map_map,Function.comp_def] at h
    change cs1.map (fun c=>c.row.val)=PSem_RoundCalls.rows.map UScalar.val at h
    exact h.trans (by rfl)
  have initHash : t0.hash=() := Subsingleton.elim _ _
  have rawPublic := (S1SemanticCode.publicTranscript_erasure D pub () pre.c1_root).symm.trans initialized
  obtain ⟨init⟩ := public_success_has_init_call D pub pre.c1_root t0 (by simpa only [initHash] using rawPublic)
  have initLog : observe (run (S1SemanticCode.publicTranscript D pub () pre.c1_root)).1=[initPair init] := by
    simpa only [initHash] using F3R_PublicLog.log init
  refine ⟨pre,t0,t25,t26,t27,cs0++cs1,init,r25,r26,z0,z1,parsed,rawPublic,
    F3R_TraceAppend.append trace0 trace1,?_,read25,
    (S1SemanticCode.circleValidated_erasure B D t25 r25).symm.trans circle25,read26,
    (S1SemanticCode.circleValidated_erasure B D t26 r26).symm.trans circle26,transcript,?_⟩
  · rw [List.map_append,order0,order1]
    rfl
  · rw [logs,initLog,F3R_BeginTrace.log trace0 order0,finishLog,
      F3R_RoundsTrace.log R trace1 order1 _ rounds]
    simp only [sourceLog,List.flatMap_append,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc]

#print axioms log
end AspisR1.F3R_VerifyLog
end
