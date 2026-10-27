import F3R_FinishTailCode
import F3R_Try
import F3K_CodeBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_FinishTail
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
attribute [local irreducible] S1SemanticCode.circleValidated

theorem split (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) (challenges : r1_wire.Challenges)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (extra : Array aspis_core.field.QM31 29#usize) (stateBefore : Array U8 32#usize)
    (z0 : aspis_core.circle.SecureCirclePoint) (t26 : r1_wire.SemanticTranscript H)
    (sem : r1_semantic.Verified H)
    (success : erase (F3R_FinishTailCode.code R B D pre challenges alpha claims extra stateBefore z0 t26)=ok (.Ok sem)) :
    ∃ record26 z1 t27,
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
      erase (S1SemanticCode.circleValidated B D t26 record26)=ok (.Ok z1,t27) ∧
      sem.transcript=t27 ∧
      (run (F3R_FinishTailCode.code R B D pre challenges alpha claims extra stateBefore z0 t26)).1=
        (run (S1SemanticCode.circleValidated B D t26 record26)).1 := by
  generalize eqLog : (run (F3R_FinishTailCode.code R B D pre challenges alpha claims extra stateBefore z0 t26)).1=original
  have logs := eqLog.symm
  unfold F3R_FinishTailCode.code at success logs
  obtain ⟨recordResult26,h26,s26,l26⟩ := F3Q_PreparePure.right _ _ _ success
  rw [l26] at logs
  obtain ⟨cf26,h27,s27,l27⟩ := F3Q_PreparePure.right _ _ _ s26
  rw [l27] at logs
  cases cf26 with
  | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s27; repeat' first | (solve | cases s27) | uncase_result | head_reduce s27 | split at s27)
  | Continue record26 =>
    obtain ⟨decoded26,h28,s28,l28⟩ := F3Q_PreparePure.right _ _ _ s27
    rw [l28] at logs
    obtain ⟨cfDecoded26,h29,s29,l29⟩ := F3Q_PreparePure.right _ _ _ s28
    rw [l29] at logs
    cases cfDecoded26 with
    | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s29; repeat' first | (solve | cases s29) | uncase_result | head_reduce s29 | split at s29)
    | Continue beforeZ1 =>
      obtain ⟨cf26Again,h30,s30,l30⟩ := F3Q_PreparePure.right _ _ _ s29
      rw [l30] at logs
      cases cf26Again with
      | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s30; repeat' first | (solve | cases s30) | uncase_result | head_reduce s30 | split at s30)
      | Continue record26Again =>
        obtain ⟨circleResult1,circleCall1,sCircle1,lCircle1⟩ := AuS1_Trace.success_bind _ _ _ s30
        rw [lCircle1] at logs
        rcases circleResult1 with ⟨circleValue1,t27⟩
        obtain ⟨cfCircle1,h31,s31,l31⟩ := F3Q_PreparePure.right _ _ _ sCircle1
        rw [l31] at logs
        cases cfCircle1 with
        | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s31; repeat' first | (solve | cases s31) | uncase_result | head_reduce s31 | split at s31)
        | Continue z1 =>
          obtain ⟨mark5,h32,s32,l32⟩ := F3Q_PreparePure.right _ _ _ s31
          rw [l32] at logs
          obtain ⟨equalPoints,h33,s33,l33⟩ := F3Q_PreparePure.right _ _ _ s32
          rw [l33] at logs
          cases equalPoints with
          | true => (simp only [erase_bind,erase_lift,erase_pure] at s33; repeat' first | (solve | cases s33) | uncase_result | head_reduce s33 | split at s33)
          | false =>
            try simp only [Bool.false_eq_true,if_false] at s33 logs
            obtain ⟨payload,h34,s34,l34⟩ := F3Q_PreparePure.right _ _ _ s33
            rw [l34] at logs
            obtain ⟨cfPayload,h35,s35,l35⟩ := F3Q_PreparePure.right _ _ _ s34
            rw [l35] at logs
            cases cfPayload with
            | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s35; repeat' first | (solve | cases s35) | uncase_result | head_reduce s35 | split at s35)
            | Continue payloadValue =>
              obtain ⟨rootResult,h36,s36,l36⟩ := F3Q_PreparePure.right _ _ _ s35
              rw [l36] at logs
              obtain ⟨root,h37,s37,l37⟩ := F3Q_PreparePure.right _ _ _ s36
              rw [l37] at logs
              have first := F3R_Try.continued recordResult26 record26 h27
              have second := F3R_Try.continued recordResult26 record26Again h30
              have same : record26Again=record26 := core.result.Result.Ok.inj (second.symm.trans first)
              subst record26Again
              have value := F3R_Try.continued circleValue1 z1 h31
              rw [value] at circleCall1
              have returned := core.result.Result.Ok.inj (Result.ok.inj s37)
              refine ⟨record26,z1,t27,h26.trans (congrArg ok first),circleCall1,?_,?_⟩
              · exact (congrArg (fun s : r1_semantic.Verified H=>s.transcript) returned).symm
              · simpa only [Pure.pure,run,List.append_nil] using logs

#print axioms split
end AspisR1.F3R_FinishTail
end
