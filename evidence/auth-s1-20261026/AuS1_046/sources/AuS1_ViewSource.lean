import AuS1_View
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_ViewSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation

 theorem folded (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1 = ok (.Ok view)) :
    ∃ (root : Array U8 32#usize) (start finish : Usize) (part : Slice U8),
      view.folded_root = some root ∧
      AspisR1SelectedWideViewV1.compact.OFF_FOLDED_ROOT = ok start ∧
      AspisR1SelectedWideViewV1.compact.OFF_ROUND1 = ok finish ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start,«end»:=finish} = ok part ∧ root.val = part.val := by
  unfold sourceView at accepted
  cases source : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1 with
  | fail e => simp only [source,bind_tc_fail] at accepted; cases accepted
  | div => simp only [source,bind_tc_div] at accepted; cases accepted
  | ok r => cases r with
    | Err e => simp only [source,bind_tc_ok] at accepted; cases accepted
    | Ok old =>
      simp only [source,bind_tc_ok] at accepted
      have same : selectedView old = view := core.result.Result.Ok.inj (Result.ok.inj accepted)
      obtain ⟨root,start,finish,part,field,hs,hf,range,bytes⟩ := AuS1_View.wide_folded proof semantic y1 old source
      refine ⟨root,start,finish,part,?_,hs,hf,range,bytes⟩
      rw [←same]
      exact field

#print axioms folded
end AspisR1.AuS1_ViewSource
end
