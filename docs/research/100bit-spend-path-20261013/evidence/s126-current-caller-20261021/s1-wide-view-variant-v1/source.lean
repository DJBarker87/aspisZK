import S1ClosedPreparationInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1SelectedWideViewV1

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B}
    {out : B} (h : (do let x ← r; f x)=ok out) :
    ∃ x, r=ok x ∧ f x=ok out := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- The reached View itself supplies S2; no independent variant premise. -/
theorem wide_view_variant (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) : out.variant=.S2 := by
  unfold verifier.candidate.wide_view at h
  obtain ⟨i,hi,h⟩ := bind_ok_inv h
  obtain ⟨i1,hi1,h⟩ := bind_ok_inv h
  obtain ⟨bytes,hbytes,h⟩ := bind_ok_inv h
  obtain ⟨parsed,hparsed,h⟩ := bind_ok_inv h
  cases parsed with
  | none =>
    simp [viewOptionOkOr,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | some x =>
    simp only [viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨i2,hi2,h⟩ := bind_ok_inv h
    obtain ⟨s1,hs1,h⟩ := bind_ok_inv h
    obtain ⟨i3,hi3,h⟩ := bind_ok_inv h
    obtain ⟨s2,hs2,h⟩ := bind_ok_inv h
    obtain ⟨r1,hr1,h⟩ := bind_ok_inv h
    obtain ⟨a,ha,h⟩ := bind_ok_inv h
    obtain ⟨i4,hi4,h⟩ := bind_ok_inv h
    obtain ⟨s3,hs3,h⟩ := bind_ok_inv h
    obtain ⟨i5,hi5,h⟩ := bind_ok_inv h
    obtain ⟨s4,hs4,h⟩ := bind_ok_inv h
    obtain ⟨s5,hs5,h⟩ := bind_ok_inv h
    have same := core.result.Result.Ok.inj (Result.ok.inj h)
    exact (congrArg verifier.View.variant same).symm

#print axioms wide_view_variant
end AspisR1SelectedWideViewV1
namespace AspisR1CurrentCaller.InstalledPreparation

theorem sourceView_variant (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view)) : view.variant=.S2 := by
  unfold sourceView at accepted
  cases source : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1 with
  | fail e => simp only [source,bind_tc_fail] at accepted; cases accepted
  | div => simp only [source,bind_tc_div] at accepted; cases accepted
  | ok r =>
    cases r with
    | Err e => simp only [source,bind_tc_ok] at accepted; cases accepted
    | Ok old =>
      simp only [source,bind_tc_ok] at accepted
      have same : selectedView old=view := core.result.Result.Ok.inj (Result.ok.inj accepted)
      rw [←same]
      have variant := AspisR1SelectedWideViewV1.wide_view_variant proof semantic y1 old source
      change (match old.variant with | .S1 => .S1 | .S2 => .S2 | .D => .D)=_
      rw [variant]

#print axioms sourceView_variant
end AspisR1CurrentCaller.InstalledPreparation
