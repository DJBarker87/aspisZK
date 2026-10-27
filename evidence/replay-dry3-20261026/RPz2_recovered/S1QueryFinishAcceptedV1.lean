import S1QueryFinishProgramV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result ControlFlow

private theorem bind_success {A B : Type} (p : Result A) (k : A → Result B)
    (out : B) (h : (p >>= k)=ok out) : ∃ value,p=ok value ∧ k value=ok out := by
  cases p with
  | ok value => exact ⟨value,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Same successful original finish result supplies the decoder output and
full returned transcript. No separate decoder or embedding success premise. -/
theorem finish_accepted (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (absorbed after : transcript.Transcript H) (blocks advances : Blocks8)
    (queries : Array U32 22#usize)
    (success : finish (M := Result) B D absorbed blocks advances=ok (.Ok queries,after)) :
    ∃ next,B.decode blocks advances=ok (.Ok (queries,next)) ∧ after={absorbed with state:=next} := by
  unfold finish at success
  obtain ⟨decoded,hdecode,success⟩ := bind_success (B.decode blocks advances) _ _ success
  cases decoded with
  | Err error =>
    simp only [core.result.Result.map_err,
      transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError,
      transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame.from,bind_tc_ok,liftM,monadLift] at success
    cases success
  | Ok pair =>
    rcases pair with ⟨query,next⟩
    simp only [core.result.Result.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,liftM,monadLift,bind_tc_ok] at success
    repeat' (obtain ⟨value,hvalue,success⟩ := bind_success _ _ _ success)
    have equal := Result.ok.inj success
    cases equal
    exact ⟨next,hdecode,rfl⟩

#print axioms finish_accepted
end AspisR1PublicPreparation.PreparedQueryMaterialize
