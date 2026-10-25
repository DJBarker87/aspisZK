import PAln_Offsets
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_ViewCuts
open AspisR1SelectedWideViewV1
open PSem_Control

theorem selected (proof semantic y1 : Slice U8) (out : verifier.View)
    (accepted : verifier.candidate.wide_view proof semantic y1=ok (.Ok out)) :
    ∃ (inactive rootBytes : Slice U8)
      (rootResult : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError)
      (root : Array U8 32#usize),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7495#usize,«end»:=7527#usize}=ok inactive ∧
      viewFromBytes inactive=ok (some out.inactive) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7527#usize,«end»:=7751#usize}=ok out.round0 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize}=ok rootBytes ∧
      core.array.TryFromSharedArraySlice.try_from 32#usize rootBytes=ok rootResult ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError rootResult=ok root ∧
      out.folded_root=some root ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7783#usize,«end»:=8007#usize}=ok out.round1 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=8007#usize,«end»:=10055#usize}=ok out.final_message := by
  unfold verifier.candidate.wide_view at accepted
  obtain ⟨i,hi,h⟩ := bind_success _ _ _ accepted
  obtain ⟨i1,hi1,h⟩ := bind_success _ _ _ h
  obtain ⟨bytes,hbytes,h⟩ := bind_success _ _ _ h
  obtain ⟨parsed,hparsed,h⟩ := bind_success _ _ _ h
  cases parsed with
  | none =>
    simp [viewOptionOkOr,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | some x =>
    simp only [viewOptionOkOr,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at h
    obtain ⟨i2,hi2,h⟩ := bind_success _ _ _ h
    obtain ⟨s1,hs1,h⟩ := bind_success _ _ _ h
    obtain ⟨i3,hi3,h⟩ := bind_success _ _ _ h
    obtain ⟨s2,hs2,h⟩ := bind_success _ _ _ h
    obtain ⟨r1,hr1,h⟩ := bind_success _ _ _ h
    obtain ⟨a,ha,h⟩ := bind_success _ _ _ h
    obtain ⟨i4,hi4,h⟩ := bind_success _ _ _ h
    obtain ⟨s3,hs3,h⟩ := bind_success _ _ _ h
    obtain ⟨i5,hi5,h⟩ := bind_success _ _ _ h
    obtain ⟨s4,hs4,h⟩ := bind_success _ _ _ h
    obtain ⟨s5,hs5,h⟩ := bind_success _ _ _ h
    have same := core.result.Result.Ok.inj (Result.ok.inj h)
    obtain ⟨off0,off1,off2,off3,off4,off5⟩ := PAln_Offsets.offsets
    have e0 := Result.ok.inj (off0.symm.trans hi)
    have e1 := Result.ok.inj (off1.symm.trans hi1)
    have e2 := Result.ok.inj (off2.symm.trans hi2)
    have e3 := Result.ok.inj (off3.symm.trans hi3)
    have e4 := Result.ok.inj (off4.symm.trans hi4)
    have e5 := Result.ok.inj (off5.symm.trans hi5)
    subst i;subst i1;subst i2;subst i3;subst i4;subst i5
    rw [← same]
    exact ⟨bytes,s2,r1,a,hbytes,hparsed,hs1,hs2,hr1,ha,rfl,hs3,hs4⟩

theorem current (proof semantic y1 : Slice U8) (out : AspisR1CurrentCaller.verifier.View)
    (accepted : AspisR1CurrentCaller.InstalledPreparation.sourceView proof semantic y1=ok (.Ok out)) :
    ∃ selected : verifier.View, verifier.candidate.wide_view proof semantic y1=ok (.Ok selected) ∧
      AspisR1CurrentCaller.InstalledPreparation.selectedView selected=out := by
  unfold AspisR1CurrentCaller.InstalledPreparation.sourceView at accepted
  cases source : verifier.candidate.wide_view proof semantic y1 with
  | fail e => simp only [source,bind_tc_fail] at accepted;cases accepted
  | div => simp only [source,bind_tc_div] at accepted;cases accepted
  | ok r =>
    cases r with
    | Err e => simp only [source,bind_tc_ok] at accepted;cases accepted
    | Ok selected =>
      simp only [source,bind_tc_ok] at accepted
      exact ⟨selected,rfl,core.result.Result.Ok.inj (Result.ok.inj accepted)⟩

#print axioms selected
#print axioms current
end AspisR1.PAln_ViewCuts
