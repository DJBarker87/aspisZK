import RPz7_SdkD_PhysicalRoots
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.AuS1_View
open AspisR1SelectedWideViewV1

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B}
    {out : B} (h : (do let x ← r; f x)=ok out) :
    ∃ x, r=ok x ∧ f x=ok out := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- The reached View retains this exact semantic slice; no independent field-equality premise. -/
theorem wide_folded (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    ∃ (root : Array U8 32#usize) (start finish : Usize) (part : Slice U8),
      out.folded_root = some root ∧
      compact.OFF_FOLDED_ROOT = ok start ∧ compact.OFF_ROUND1 = ok finish ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start,«end»:=finish} = ok part ∧ root.val = part.val := by
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
    have field : out.folded_root = some a := (congrArg verifier.View.folded_root same).symm
    refine ⟨a,i2,i3,s2,field,hi2,hi3,hs2,?_⟩
    unfold core.array.TryFromSharedArraySlice.try_from at hr1
    split at hr1
    · have r1eq := Result.ok.inj hr1
      subst r1
      change ok _ = ok a at ha
      exact (congrArg Subtype.val (Result.ok.inj ha)).symm
    · have r1eq := Result.ok.inj hr1
      subst r1
      cases ha

#print axioms wide_folded
end AspisR1.AuS1_View
