import PSem_SemanticTrace
set_option autoImplicit false
namespace AspisR1.F3M_SemanticSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation r1_wire
theorem values (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify R B D pub bytes hash=ok (.Ok sem)) :
    ∃ (pre : Prefix) (t0 t15 t25 : SemanticTranscript H) (cs : List (SourceFull25.Call
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) pre)),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      r1_semantic.public_transcript (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
        (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) hash pre.c1_root=ok (.Ok t0) ∧
      SourceFull25.Trace (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) pre t0 t25 cs ∧
      cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map SourceFull25.Call.q=BeginCalls.challengeList (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem).challenges ++ (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem).alpha.val ∧
      cs.map (fun c => c.record.framed) = pre.records.val.take 25 ∧
      ∃ record25 record26 z0 t26 z1 t27,
        Prefix.validated_record pre 25#u8=ok (.Ok record25) ∧
        FinishModel.circle_validated (S1SemanticRootCopy.install B)
          (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) t25 record25=ok (.Ok z0,t26) ∧
        Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
        FinishModel.circle_validated (S1SemanticRootCopy.install B)
          (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) t26 record26=ok (.Ok z1,t27) ∧
        (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem).transcript=t27 ∧
        (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem).z=Array.make 2#usize [z0,z1] := by
  obtain ⟨pre,t0,t15,challenges,payload,root,parsed,publicInit,begin,finish,_⟩ :=
    AspisR1CurrentCaller.S1SemanticInstallation.verify_roots R B D pub bytes hash sem success
  obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,challengeEq,stateEq,trEq,claims,rec25,decode25,circle25,rec26,decode26,circle26,zEq⟩ :=
    S1SemanticFinishBounds.finish_success R (S1SemanticRootCopy.install B)
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
      (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) pre t15 challenges none
      (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) finish
  obtain ⟨qs0,run0,eq0⟩ := BeginCalls.begin_success
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) pre t0 t15 challenges begin
  obtain ⟨qs1,run1,eq1⟩ := PSem_RoundCalls.rounds_success R
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D) pre t15 t25 running
    (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem).alpha rounds
  have run := PSem_SemanticTrace.semantic_append _ _ run0 run1
  have rowOrder : (BeginCalls.rows++PSem_RoundCalls.rows).map UScalar.val=List.range 25 := by rfl
  obtain ⟨cs,trace,rows,qs,frames⟩ := SourceFull25.run_full25_frames _ pre run rowOrder
  have rowValues := congrArg (List.map UScalar.val) rows
  exact ⟨pre,t0,t15,t25,cs,parsed,publicInit,trace,
    by simpa only [List.map_map,Function.comp_def,rowOrder] using rowValues,by rw [qs,eq0,eq1,challengeEq],frames,
    record25,record26,z0,t26,z1,t27,rec25,circle25,rec26,circle26,trEq,zEq⟩

#print axioms values
end AspisR1.F3M_SemanticSource
