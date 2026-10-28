import NBA_WideView
import NBA_Inactive
set_option autoImplicit false
namespace AspisR1.NBL_ViewFields
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1
/-- Invert the actual selected producer, keeping original semantic/y1 carriers.
No successful output field is stipulated separately. -/
theorem source (proof semantic y1 : Slice U8) (out : AspisR1SelectedWideViewV1.verifier.View)
    (h : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    out.y1=y1 ∧ out.semantic=semantic ∧ out.variant=.S2 ∧
      ∃ root, out.folded_root=some root := by
  unfold AspisR1SelectedWideViewV1.verifier.candidate.wide_view at h
  obtain ⟨i,hi,h⟩ := NBA_Inactive.bind_success _ _ _ h
  obtain ⟨i1,hi1,h⟩ := NBA_Inactive.bind_success _ _ _ h
  obtain ⟨bytes,hbytes,h⟩ := NBA_Inactive.bind_success _ _ _ h
  obtain ⟨parsed,hparsed,h⟩ := NBA_Inactive.bind_success _ _ _ h
  cases parsed with
  | none =>
    simp [viewOptionOkOr,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | some x =>
    simp only [viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨i2,hi2,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨s1,hs1,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨i3,hi3,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨s2,hs2,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨r1,hr1,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨a,ha,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨i4,hi4,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨s3,hs3,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨i5,hi5,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨s4,hs4,h⟩ := NBA_Inactive.bind_success _ _ _ h
    obtain ⟨s5,hs5,h⟩ := NBA_Inactive.bind_success _ _ _ h
    have hout := core.result.Result.Ok.inj (Result.ok.inj h)
    have hy := congrArg AspisR1SelectedWideViewV1.verifier.View.y1 hout
    have hs := congrArg AspisR1SelectedWideViewV1.verifier.View.semantic hout
    have hv := congrArg AspisR1SelectedWideViewV1.verifier.View.variant hout
    have hf := congrArg AspisR1SelectedWideViewV1.verifier.View.folded_root hout
    exact ⟨hy.symm,hs.symm,hv.symm,⟨a,hf.symm⟩⟩

#print axioms source
end AspisR1.NBL_ViewFields
