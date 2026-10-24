import S1WideViewVariantV1
import S1AcceptedSliceRangeV1
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

/-- The reached View supplies the SAME final-message frame and range guards.
No independently selected slice, range or parser success is supplied. -/
theorem wide_view_final_frame (proof semantic y1 : Slice U8) (out : verifier.View)
    (h : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    ∃ (start stop : Usize), compact.OFF_FINAL=ok start ∧ compact.OFF_OPENINGS=ok stop ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=start,«end»:=stop}=ok out.final_message ∧
      start.val ≤ stop.val ∧ stop.val ≤ proof.length ∧ out.final_message.length=stop.val-start.val := by
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
    have finalEq : s4=out.final_message := congrArg verifier.View.final_message same
    have frame := AspisS1AcceptedSliceRange.accepted_range proof s4 i4 i5 hs4
    exact ⟨i4,i5,hi4,hi5,finalEq ▸ hs4,frame.1,frame.2.1,finalEq ▸ frame.2.2⟩

#print axioms wide_view_final_frame
end AspisR1SelectedWideViewV1
