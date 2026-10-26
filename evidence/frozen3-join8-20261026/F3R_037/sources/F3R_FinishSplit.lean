import F3R_Pure
import F3K_CodeBind
import S1SemanticCodeFinishExactV1
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
  rw [l0,AuS1_Trace.observe_append]
  cases roundResult with
  | Err e => (simp only [erase_bind,erase_lift,erase_pure] at s0; repeat' first | (solve | cases s0) | uncase_result | head_reduce s0 | split at s0)
  | Ok roundResult =>
    rcases roundResult with ⟨running,alpha,t25⟩
    erw [F3R_Pure.erase_ok] at s0
    erw [F3K_CodeStep.pure_step]
    try simp only at s0 ⊢
    obtain ⟨mark2,h1,s1,l1⟩ := F3Q_PreparePure.right _ _ _ s0
    rw [l1]
    obtain ⟨claimsResult,h2,s2,l2⟩ := F3Q_PreparePure.right _ _ _ s1
    rw [l2]
    obtain ⟨cfClaims,h3,s3,l3⟩ := F3Q_PreparePure.right _ _ _ s2
    rw [l3]
    cases cfClaims with
    | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s3; repeat' first | (solve | cases s3) | uncase_result | head_reduce s3 | split at s3)
    | Continue claims =>
      obtain ⟨terminalResult,h4,s4,l4⟩ := F3Q_PreparePure.right _ _ _ s3
      rw [l4]
      obtain ⟨mappedTerminal,h5,s5,l5⟩ := F3Q_PreparePure.right _ _ _ s4
      rw [l5]
      obtain ⟨cfTerminal,h6,s6,l6⟩ := F3Q_PreparePure.right _ _ _ s5
      rw [l6]
      cases cfTerminal with
      | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s6; repeat' first | (solve | cases s6) | uncase_result | head_reduce s6 | split at s6)
      | Continue terminal =>
        obtain ⟨mark3,h7,s7,l7⟩ := F3Q_PreparePure.right _ _ _ s6
        rw [l7]
        obtain ⟨a,h8,s8,l8⟩ := F3Q_PreparePure.right _ _ _ s7
        rw [l8]
        obtain ⟨a1,h9,s9,l9⟩ := F3Q_PreparePure.right _ _ _ s8
        rw [l9]
        obtain ⟨a2,h10,s10,l10⟩ := F3Q_PreparePure.right _ _ _ s9
        rw [l10]
        obtain ⟨q,h11,s11,l11⟩ := F3Q_PreparePure.right _ _ _ s10
        rw [l11]
        obtain ⟨mask,h12,s12,l12⟩ := F3Q_PreparePure.right _ _ _ s11
        rw [l12]
        obtain ⟨recordResult25,h13,s13,l13⟩ := F3Q_PreparePure.right _ _ _ s12
        rw [l13]
        obtain ⟨cf25,h14,s14,l14⟩ := F3Q_PreparePure.right _ _ _ s13
        rw [l14]
        cases cf25 with
        | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s14; repeat' first | (solve | cases s14) | uncase_result | head_reduce s14 | split at s14)
        | Continue record25 =>
          skip
          obtain ⟨decoded25,h15,s15,l15⟩ := F3Q_PreparePure.right _ _ _ s14
          rw [l15]
          obtain ⟨cfDecoded25,h16,s16,l16⟩ := F3Q_PreparePure.right _ _ _ s15
          rw [l16]
          cases cfDecoded25 with
          | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s16; repeat' first | (solve | cases s16) | uncase_result | head_reduce s16 | split at s16)
          | Continue extra =>
            obtain ⟨q1,h17,s17,l17⟩ := F3Q_PreparePure.right _ _ _ s16
            rw [l17]
            obtain ⟨q2,h18,s18,l18⟩ := F3Q_PreparePure.right _ _ _ s17
            rw [l18]
            obtain ⟨q3,h19,s19,l19⟩ := F3Q_PreparePure.right _ _ _ s18
            rw [l19]
            obtain ⟨maskedTerminal,h20,s20,l20⟩ := F3Q_PreparePure.right _ _ _ s19
            rw [l20]
            obtain ⟨bad,h21,s21,l21⟩ := F3Q_PreparePure.right _ _ _ s20
            rw [l21]
            cases bad with
            | true => (simp only [erase_bind,erase_lift,erase_pure] at s21; repeat' first | (solve | cases s21) | uncase_result | head_reduce s21 | split at s21)
            | false =>
              try simp only [Bool.false_eq_true,if_false] at s21 ⊢
              obtain ⟨mark4,h22,s22,l22⟩ := F3Q_PreparePure.right _ _ _ s21
              rw [l22]
              obtain ⟨stateBefore,h23,s23,l23⟩ := F3Q_PreparePure.right _ _ _ s22
              rw [l23]
              obtain ⟨cf25Again,h24,s24,l24⟩ := F3Q_PreparePure.right _ _ _ s23
              rw [l24]
              cases cf25Again with
              | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s24; repeat' first | (solve | cases s24) | uncase_result | head_reduce s24 | split at s24)
              | Continue record25Again =>
                obtain ⟨circleResult0,circleCall0,sCircle0,lCircle0⟩ := AuS1_Trace.success_bind _ _ _ s24
                rw [lCircle0,AuS1_Trace.observe_append]
                rcases circleResult0 with ⟨circleValue0,t26⟩
                obtain ⟨cfCircle0,h25,s25,l25⟩ := F3Q_PreparePure.right _ _ _ sCircle0
                rw [l25]
                cases cfCircle0 with
                | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s25; repeat' first | (solve | cases s25) | uncase_result | head_reduce s25 | split at s25)
                | Continue z0 =>
                  obtain ⟨recordResult26,h26,s26,l26⟩ := F3Q_PreparePure.right _ _ _ s25
                  rw [l26]
                  obtain ⟨cf26,h27,s27,l27⟩ := F3Q_PreparePure.right _ _ _ s26
                  rw [l27]
                  cases cf26 with
                  | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s27; repeat' first | (solve | cases s27) | uncase_result | head_reduce s27 | split at s27)
                  | Continue record26 =>
                    obtain ⟨decoded26,h28,s28,l28⟩ := F3Q_PreparePure.right _ _ _ s27
                    rw [l28]
                    obtain ⟨cfDecoded26,h29,s29,l29⟩ := F3Q_PreparePure.right _ _ _ s28
                    rw [l29]
                    cases cfDecoded26 with
                    | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s29; repeat' first | (solve | cases s29) | uncase_result | head_reduce s29 | split at s29)
                    | Continue beforeZ1 =>
                      obtain ⟨cf26Again,h30,s30,l30⟩ := F3Q_PreparePure.right _ _ _ s29
                      rw [l30]
                      cases cf26Again with
                      | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s30; repeat' first | (solve | cases s30) | uncase_result | head_reduce s30 | split at s30)
                      | Continue record26Again =>
                        obtain ⟨circleResult1,circleCall1,sCircle1,lCircle1⟩ := AuS1_Trace.success_bind _ _ _ s30
                        rw [lCircle1,AuS1_Trace.observe_append]
                        rcases circleResult1 with ⟨circleValue1,t27⟩
                        obtain ⟨cfCircle1,h31,s31,l31⟩ := F3Q_PreparePure.right _ _ _ sCircle1
                        rw [l31]
                        cases cfCircle1 with
                        | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s31; repeat' first | (solve | cases s31) | uncase_result | head_reduce s31 | split at s31)
                        | Continue z1 =>
                          obtain ⟨mark5,h32,s32,l32⟩ := F3Q_PreparePure.right _ _ _ s31
                          rw [l32]
                          obtain ⟨equalPoints,h33,s33,l33⟩ := F3Q_PreparePure.right _ _ _ s32
                          rw [l33]
                          cases equalPoints with
                          | true => (simp only [erase_bind,erase_lift,erase_pure] at s33; repeat' first | (solve | cases s33) | uncase_result | head_reduce s33 | split at s33)
                          | false =>
                            try simp only [Bool.false_eq_true,if_false] at s33 ⊢
                            obtain ⟨payload,h34,s34,l34⟩ := F3Q_PreparePure.right _ _ _ s33
                            rw [l34]
                            obtain ⟨cfPayload,h35,s35,l35⟩ := F3Q_PreparePure.right _ _ _ s34
                            rw [l35]
                            cases cfPayload with
                            | Break residual => (simp only [erase_bind,erase_lift,erase_pure] at s35; repeat' first | (solve | cases s35) | uncase_result | head_reduce s35 | split at s35)
                            | Continue payloadValue =>
                              obtain ⟨rootResult,h36,s36,l36⟩ := F3Q_PreparePure.right _ _ _ s35
                              rw [l36]
                              obtain ⟨root,h37,s37,l37⟩ := F3Q_PreparePure.right _ _ _ s36
                              rw [l37]
                              trace_state

#print axioms split
end AspisR1.F3R_FinishSplit
end
