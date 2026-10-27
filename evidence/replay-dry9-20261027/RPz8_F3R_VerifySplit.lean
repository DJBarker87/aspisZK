import RPz8_F3R_FinishSplit
import RPz8_F3R_Try
import RPz8_F3Q_PreparePure
import RPz7_S1SemanticCodeVerifyExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_VerifySplit
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode
attribute [local irreducible] S1SemanticCode.begin S1SemanticCode.finish S1SemanticCode.publicTranscript

theorem split (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (sem : r1_semantic.Verified H)
    (success : erase (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes hash none)=ok (.Ok sem)) :
    ∃ pre t0 t15 challenges,
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      erase (S1SemanticCode.publicTranscript D pub hash pre.c1_root)=ok (.Ok t0) ∧
      erase (S1SemanticCode.begin D pre t0)=ok (.Ok challenges,t15) ∧
      erase (S1SemanticCode.finish R B D pub pre t15 challenges none)=ok (.Ok sem) ∧
      observe (run (S1SemanticCode.verify (S1SemanticCode.finish R B) D pub bytes hash none)).1=
        observe (run (S1SemanticCode.publicTranscript D pub hash pre.c1_root)).1 ++
        (observe (run (S1SemanticCode.begin D pre t0)).1 ++
          observe (run (S1SemanticCode.finish R B D pub pre t15 challenges none)).1) := by
  unfold S1SemanticCode.verify at success ⊢
  obtain ⟨parsed,hparsed,s0,l0⟩ := F3Q_PreparePure.right _ _ _ success
  have logs := l0
  obtain ⟨cf,hcf,s1,l1⟩ := F3Q_PreparePure.right _ _ _ s0
  rw [l1] at logs
  cases cf with
  | Break residual =>
    simp only [erase_bind,erase_lift,erase_pure] at s1
    repeat' first | (solve | cases s1) | uncase_result | head_reduce s1 | split at s1
  | Continue pre =>
    obtain ⟨mark0,hmark0,s2,l2⟩ := F3Q_PreparePure.right _ _ _ s1
    rw [l2] at logs
    obtain ⟨publicResult,hpublic,s3,l3⟩ := AuS1_Trace.success_bind _ _ _ s2
    rw [l3] at logs
    obtain ⟨cfPublic,hcfPublic,s4,l4⟩ := F3Q_PreparePure.right _ _ _ s3
    rw [l4] at logs
    cases cfPublic with
    | Break residual =>
      simp only [erase_bind,erase_lift,erase_pure] at s4
      repeat' first | (solve | cases s4) | uncase_result | head_reduce s4 | split at s4
    | Continue t0 =>
      obtain ⟨beginResult,hbegin,s5,l5⟩ := AuS1_Trace.success_bind _ _ _ s4
      rw [l5] at logs
      rcases beginResult with ⟨beginValue,t15⟩
      obtain ⟨cfBegin,hcfBegin,s6,l6⟩ := F3Q_PreparePure.right _ _ _ s5
      rw [l6] at logs
      cases cfBegin with
      | Break residual =>
        simp only [erase_bind,erase_lift,erase_pure] at s6
        repeat' first | (solve | cases s6) | uncase_result | head_reduce s6 | split at s6
      | Continue challenges =>
        obtain ⟨mark1,hmark1,s7,l7⟩ := F3Q_PreparePure.right _ _ _ s6
        rw [l7] at logs
        rw [F3R_Try.continued publicResult t0 hcfPublic] at hpublic
        rw [F3R_Try.continued beginValue challenges hcfBegin] at hbegin
        refine ⟨pre,t0,t15,challenges,hparsed.trans (congrArg ok (F3R_Try.continued parsed pre hcf)),
          hpublic,hbegin,s7,?_⟩
        exact (congrArg observe logs).trans (by simp only [AuS1_Trace.observe_append,List.append_assoc])

#print axioms split
end AspisR1.F3R_VerifySplit
end
