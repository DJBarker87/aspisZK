import RPz7_PAln_Physical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_RootConvert
open MultiproofConeCanonical OraclePortCompactDraft

theorem shared {T : Type} (n : Usize) (input : Slice T)
    (result : core.result.Result (Array T n) core.array.TryFromSliceError)
    (root : Array T n)
    (converted : core.array.TryFromSharedArraySlice.try_from n input=ok result)
    (unwrapped : core.result.Result.unwrap core.fmt.DebugTryFromSliceError result=ok root) :
    root.val=input.val := by
  cases result with
  | Err e => cases unwrapped
  | Ok value =>
    have same : value=root := Result.ok.inj unwrapped
    subst value
    unfold core.array.TryFromSharedArraySlice.try_from at converted
    split at converted
    · have same := core.result.Result.Ok.inj (Result.ok.inj converted)
      exact (congrArg Subtype.val same).symm
    · cases converted

theorem source (proof semantic y1 : Slice U8) (view : AspisR1SelectedWideViewV1.verifier.View)
    (accepted : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view)) :
    ∃ root,view.folded_root=some root ∧ bytesOf root.val=slice (bytesOf proof.val) 7751 32 := by
  obtain ⟨inactive,rootBytes,result,root,hi,hp,h0,hr,converted,unwrapped,rootEq,h1,hf⟩ :=
    PAln_ViewCuts.selected proof semantic y1 view accepted
  have rootVal := shared 32#usize rootBytes result root converted unwrapped
  have start : (7751#usize).val=7751 := by scalar_tac
  have stop : (7783#usize).val=7783 := by scalar_tac
  refine ⟨root,rootEq,?_⟩
  rw [rootVal]
  simpa only [start,stop] using PAln_Physical.range_bytes proof rootBytes 7751#usize 7783#usize hr

#print axioms shared
#print axioms source
end AspisR1.PAln_RootConvert
