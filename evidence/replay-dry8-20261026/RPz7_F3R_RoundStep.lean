import RPz7_F3R_SemanticChain
import RPz7_F3R_Result
import RPz7_S1SemanticCodeRoundStepExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_RoundStep
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceDigestLog
attribute [local irreducible] S1SemanticCode.semanticValidated

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (B : RoundModel.Boundaries) (c : SourceFull25.Call D pre) (below : c.row.val<25)
    (alpha : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31)
    (round : Usize) (row : 15#u8+UScalar.cast .U8 round=ok c.row)
    (out : aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × r1_wire.SemanticTranscript Hash)
    (success : erase (S1SemanticCode.roundStep B D pre c.before alpha running round)=ok (.Ok out)) :
    observe (run (S1SemanticCode.roundStep B D pre c.before alpha running round)).1=callLog c := by
  have ret := F3R_SemanticStep.returned c below
  unfold S1SemanticCode.roundStep at success ⊢
  simp only [erase_bind,erase_lift,lift,bind_tc_ok,row,c.validated,
    core.result.Result.Insts.CoreOpsTry.branch] at success
  obtain ⟨poly,decoded,s1⟩ := F3R_Result.bind_success _ _ _ success
  cases poly with
  | Err e =>
    simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at s1
    cases s1
  | Ok poly =>
    simp only [erase_bind,erase_lift,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at s1
    obtain ⟨boundary,hb,s2⟩ := F3R_Result.bind_success _ _ _ s1
    obtain ⟨bad,hbad,s3⟩ := F3R_Result.bind_success _ _ _ s2
    cases bad with
    | true => simp only [if_true,erase_pure] at s3;cases s3
    | false =>
      try simp only [Bool.false_eq_true,if_false,erase_bind,erase_lift,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at s3
      rw [ret] at s3
      simp only [bind_tc_ok,erase_bind,erase_lift,core.result.Result.Insts.CoreOpsTry.branch] at s3
      obtain ⟨updated,update,s4⟩ := F3R_Result.bind_success _ _ _ s3
      obtain ⟨value,hvalue,s5⟩ := F3R_Result.bind_success _ _ _ s4
      simp only [lift]
      erw [F3K_CodeStep.pure_step]
      rw [row]
      erw [F3K_CodeStep.pure_step]
      rw [c.validated]
      erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
      try simp only
      rw [decoded]
      erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
      try simp only
      erw [F3K_CodeStep.lift_success _ _ hb,F3K_CodeStep.lift_success _ _ hbad]
      simp only [Bool.false_eq_true,if_false]
      erw [F3K_CodeStep.pure_step,F3K_CodeBind.success _ _ _ ret]
      try simp only
      erw [F3K_CodeStep.pure_step]
      erw [F3K_CodeStep.lift_success _ _ update,F3K_CodeStep.lift_success _ _ hvalue]
      change observe (run (S1SemanticCode.semanticValidated D c.before c.record)).1++[]=_
      rw [F3J_ValidatedLog.semantic c below,List.append_nil]

#print axioms log
end AspisR1.F3R_RoundStep
end
