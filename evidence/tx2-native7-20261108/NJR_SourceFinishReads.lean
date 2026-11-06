import NJR_SuccessReads
set_option autoImplicit false
noncomputable section
namespace NJR_SourceFinishReads
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Stage2Finish

/-- Only acceptance inversion of the same complete source body. The witnesses
are derived, not successful-child or endpoint hypotheses at a positive root. -/
theorem rounds {W : Type} (ops : FinishOps W) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (folds : ops.folds p.variant=ok 2#usize)
 (run : verifier.finishRelationWithOps ops v p a none=ok (.Ok ())) :
 ∃ alpha0 alpha1 claim0 claim1,
 verifier.finishRelationRoundWithOps ops v.round0 alpha0 p.claim 0#usize=ok (.Ok claim0) ∧
 verifier.finishRelationRoundWithOps ops v.round1 alpha1 claim0 1#usize=ok (.Ok claim1) := by
 unfold verifier.finishRelationWithOps at run
 rw [folds] at run
 obtain ⟨alpha0,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 obtain ⟨reply,first,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases reply with
 | Err e => cases run
 | Ok claim0 =>
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,if_pos rfl] at run
  obtain ⟨alpha1,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨reply,second,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases reply with
  | Err e => cases run
  | Ok claim1 => exact ⟨alpha0,alpha1,claim0,claim1,first,second⟩

/-- Source accepted finish reads both seven-field rounds and the entire dot
input on S2. It adds no raw-canonicality or no-collision premise. -/
theorem source (r : NP6_StdModel.Reservation) (v : verifier.View)
 (p : verifier.Prepared) (a : verifier.Accumulator) (s2 : p.variant=.S2)
 (width : a.weights.val.length=64)
 (run : Port4D_FinishInstall.finish (IDa_Deployed.finish r) v p a none=ok (.Ok ())) :
 (∀ i : Usize,i.val<7→∃ c,FIn_Primitives.field v.round0 i=ok c) ∧
 (∀ i : Usize,i.val<7→∃ c,FIn_Primitives.field v.round1 i=ok c) ∧
 (∀ i : Fin 64,∃ index value,index.val=i.val ∧
  AspisR1CurrentWide.Proof.finishField v.final_message index=ok value) := by
 have old : Port3_FinishStage.finish (IDa_Deployed.finish r) v p a none=ok (.Ok ()) := by
  rw [←Port4D_FinishInstall.retained_eq]
  exact run
 have actual := (Port3_QueryInstall.success_iff _ _).mp old
 rw [Port3_FinishStage.parent_eq,NIG_Slots.release] at actual
 have folds : (IDa_Deployed.finish r).folds p.variant=ok 2#usize := by rw [s2];rfl
 obtain ⟨alpha0,alpha1,claim0,claim1,round0,round1⟩:=rounds _ v p a folds actual
 have dot: SAG_DotClosed.source v.final_message a.weights.deref=ok (.Ok a.rhs) :=
  (Port3_FinishAny.accepted_dot (IDa_Deployed.finish r) v p a none old).1
 exact ⟨NJR_SuccessReads.round r v.round0 alpha0 p.claim claim0 0#usize (by change 0≤1;omega) round0,
  NJR_SuccessReads.round r v.round1 alpha1 claim0 claim1 1#usize (by change 1≤1;omega) round1,
  NJR_SuccessReads.dot v.final_message a.weights.deref a.rhs width dot⟩

#print axioms rounds
#print axioms source
end NJR_SourceFinishReads
