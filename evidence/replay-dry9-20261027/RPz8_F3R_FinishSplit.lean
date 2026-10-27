import RPz8_F3R_Pure
import RPz8_F3R_FinishTail
import RPz8_F3K_CodeBind
import RPz7_S1SemanticCodeFinishExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_FinishSplit
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
attribute [local irreducible] S1SemanticCode.rounds S1SemanticCode.circleValidated

theorem split (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {Hash : Type} (D : aspis_core.Digest32 Hash)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript Hash) (challenges : r1_wire.Challenges)
    (sem : r1_semantic.Verified Hash)
    (success : erase (S1SemanticCode.finish R B D pub pre before challenges none)=ok (.Ok sem)) :
    ∃ (running : aspis_core.field.QM31) (alpha : Array aspis_core.field.QM31 10#usize)
      (t25 : r1_wire.SemanticTranscript Hash) (record25 : r1_wire.ValidatedRecord)
      (z0 : aspis_core.circle.SecureCirclePoint) (t26 : r1_wire.SemanticTranscript Hash)
      (record26 : r1_wire.ValidatedRecord) (z1 : aspis_core.circle.SecureCirclePoint)
      (t27 : r1_wire.SemanticTranscript Hash),
      erase (S1SemanticCode.rounds R D pre before)=ok (.Ok (running,alpha,t25)) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record25) ∧
      erase (S1SemanticCode.circleValidated B D t25 record25)=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok record26) ∧
      erase (S1SemanticCode.circleValidated B D t26 record26)=ok (.Ok z1,t27) ∧
      sem.transcript=t27 ∧
      observe (run (S1SemanticCode.finish R B D pub pre before challenges none)).1=
        observe (run (S1SemanticCode.rounds R D pre before)).1 ++
        (observe (run (S1SemanticCode.circleValidated B D t25 record25)).1 ++
          observe (run (S1SemanticCode.circleValidated B D t26 record26)).1) := by
  unfold S1SemanticCode.finish at success ⊢
  obtain ⟨roundResult,roundCall,s0,l0⟩ := AuS1_Trace.success_bind _ _ _ success
  have logs := l0
  cases roundResult with
  | Err e => (simp only [erase_bind,erase_lift,erase_pure] at s0; repeat' first | (solve | cases s0) | uncase_result | head_reduce s0 | split at s0)
  | Ok roundResult =>
    rcases roundResult with ⟨running,alpha,t25⟩
    obtain ⟨cf,hcf,s0',lcf⟩ := F3Q_PreparePure.right _ _ _ s0
    have ecf : cf=core.ops.control_flow.ControlFlow.Continue (running,alpha,t25) := (Result.ok.inj hcf).symm
    subst cf
    rw [lcf] at logs
    try simp only at s0'
    clear s0
    have s0 := s0'
    obtain ⟨mark2,h1,s1,l1⟩ := F3Q_PreparePure.right _ _ _ s0
    rw [l1] at logs
    obtain ⟨claimsResult,h2,s2,l2⟩ := F3Q_PreparePure.right _ _ _ s1
    rw [l2] at logs
    obtain ⟨cfClaims,h3,s3,l3⟩ := F3Q_PreparePure.right _ _ _ s2
    rw [l3] at logs
    cases cfClaims with
    | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s3; repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3)
    | Continue claims =>
      obtain ⟨terminalResult,h4,s4,l4⟩ := F3Q_PreparePure.right _ _ _ s3
      rw [l4] at logs
      obtain ⟨mappedTerminal,h5,s5,l5⟩ := F3Q_PreparePure.right _ _ _ s4
      rw [l5] at logs
      obtain ⟨cfTerminal,h6,s6,l6⟩ := F3Q_PreparePure.right _ _ _ s5
      rw [l6] at logs
      cases cfTerminal with
      | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s6; repeat' first | (solve | cases s6) | uncase_result | head_reduce s6 | split at s6)
      | Continue terminal =>
        obtain ⟨mark3,h7,s7,l7⟩ := F3Q_PreparePure.right _ _ _ s6
        rw [l7] at logs
        obtain ⟨a,h8,s8,l8⟩ := F3Q_PreparePure.right _ _ _ s7
        rw [l8] at logs
        obtain ⟨a1,h9,s9,l9⟩ := F3Q_PreparePure.right _ _ _ s8
        rw [l9] at logs
        obtain ⟨a2,h10,s10,l10⟩ := F3Q_PreparePure.right _ _ _ s9
        rw [l10] at logs
        obtain ⟨q,h11,s11,l11⟩ := F3Q_PreparePure.right _ _ _ s10
        rw [l11] at logs
        obtain ⟨mask,h12,s12,l12⟩ := F3Q_PreparePure.right _ _ _ s11
        rw [l12] at logs
        obtain ⟨recordResult25,h13,s13,l13⟩ := F3Q_PreparePure.right _ _ _ s12
        rw [l13] at logs
        obtain ⟨cf25,h14,s14,l14⟩ := F3Q_PreparePure.right _ _ _ s13
        rw [l14] at logs
        cases cf25 with
        | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s14; repeat' first | (solve | cases s14) | uncase_result | head_reduce s14 | split at s14)
        | Continue record25 =>
          skip
          obtain ⟨decoded25,h15,s15,l15⟩ := F3Q_PreparePure.right _ _ _ s14
          rw [l15] at logs
          obtain ⟨cfDecoded25,h16,s16,l16⟩ := F3Q_PreparePure.right _ _ _ s15
          rw [l16] at logs
          cases cfDecoded25 with
          | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s16; repeat' first | (solve | cases s16) | uncase_result | head_reduce s16 | split at s16)
          | Continue extra =>
            obtain ⟨q1,h17,s17,l17⟩ := F3Q_PreparePure.right _ _ _ s16
            rw [l17] at logs
            obtain ⟨q2,h18,s18,l18⟩ := F3Q_PreparePure.right _ _ _ s17
            rw [l18] at logs
            obtain ⟨q3,h19,s19,l19⟩ := F3Q_PreparePure.right _ _ _ s18
            rw [l19] at logs
            obtain ⟨maskedTerminal,h20,s20,l20⟩ := F3Q_PreparePure.right _ _ _ s19
            rw [l20] at logs
            obtain ⟨bad,h21,s21,l21⟩ := F3Q_PreparePure.right _ _ _ s20
            rw [l21] at logs
            cases bad with
            | true => (simp only [erase_bind,erase_lift,erase_pure] at s21; repeat' first | (solve | cases s21) | uncase_result | head_reduce s21 | split at s21)
            | false =>
              try simp only [Bool.false_eq_true,if_false] at s21 logs
              obtain ⟨mark4,h22,s22,l22⟩ := F3Q_PreparePure.right _ _ _ s21
              rw [l22] at logs
              obtain ⟨stateBefore,h23,s23,l23⟩ := F3Q_PreparePure.right _ _ _ s22
              rw [l23] at logs
              obtain ⟨cf25Again,h24,s24,l24⟩ := F3Q_PreparePure.right _ _ _ s23
              rw [l24] at logs
              cases cf25Again with
              | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s24; repeat' first | (solve | cases s24) | uncase_result | head_reduce s24 | split at s24)
              | Continue record25Again =>
                obtain ⟨circleResult0,circleCall0,sCircle0,lCircle0⟩ := AuS1_Trace.success_bind _ _ _ s24
                rw [lCircle0] at logs
                rcases circleResult0 with ⟨circleValue0,t26⟩
                obtain ⟨cfCircle0,h25,s25,l25⟩ := F3Q_PreparePure.right _ _ _ sCircle0
                rw [l25] at logs
                cases cfCircle0 with
                | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s25; repeat' first | (solve | cases s25) | uncase_result | head_reduce s25 | split at s25)
                | Continue z0 =>
                  have first := F3R_Try.continued recordResult25 record25 h14
                  have second := F3R_Try.continued recordResult25 record25Again h24
                  have same : record25Again=record25 := core.result.Result.Ok.inj (second.symm.trans first)
                  subst record25Again
                  have value := F3R_Try.continued circleValue0 z0 h25
                  rw [value] at circleCall0
                  obtain ⟨record26,z1,t27,read26,circle1,transcript,tailLog⟩ :=
                    F3R_FinishTail.split R B D pre challenges alpha claims extra stateBefore z0 t26 sem s25
                  erw [tailLog] at logs
                  refine ⟨running,alpha,t25,record25,z0,t26,record26,z1,t27,roundCall,
                    h13.trans (congrArg ok first),circleCall0,read26,circle1,transcript,?_⟩
                  exact (congrArg observe logs).trans (by
                    simp only [AuS1_Trace.observe_append,List.append_assoc])

#print axioms split
end AspisR1.F3R_FinishSplit
end
