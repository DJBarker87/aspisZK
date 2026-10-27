import F3R_SemanticChain
import F3Q_PreparePure
import S1SemanticCodeRoundStepExactV1
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
  simp only [erase_bind,erase_lift,bind_tc_ok,row,c.validated,
    core.result.Result.Insts.CoreOpsTry.branch] at success
  obtain ⟨poly,decoded,s1,logs1⟩ := F3Q_PreparePure.right _ _ _ success
  cases poly with
  | Err e =>
    simp only [erase_bind,erase_lift,erase_pure,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at s1
    cases s1
  | Ok poly =>
    simp only [erase_bind,erase_lift,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at s1
    obtain ⟨boundary,hb,s2⟩ := (Aeneas.Std.bind_eq_ok_iff.mp s1)
    trace_state

#print axioms log
end AspisR1.F3R_RoundStep
end
