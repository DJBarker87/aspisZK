import NBL_ViewNatural
import NBA_WideView
set_option autoImplicit false
namespace AspisR1.NBL_ViewDomains
open Aeneas Aeneas.Std Result AspisR1SelectedWideViewV1

/-- All fixed opening payload sizes and pass-through carriers are consequences
of the SAME selected producer on the frozen full-proof domain. -/
theorem source (proof semantic y1 : Slice U8) (full : proof.val.length=57607)
    (view : verifier.View)
    (call : verifier.candidate.wide_view proof semantic y1=ok (.Ok view)) :
    view.semantic=semantic ∧ view.y1=y1 ∧ view.variant=.S2 ∧
    view.round0.val.length=224 ∧ view.round1.val.length=224 ∧
    view.final_message.val.length=2048 ∧
    ∃ root : Array U8 32#usize,view.folded_root=some root ∧
      root.val=(proof.val.drop 7751).take 32 := by
  have size : 10055≤proof.val.length := by omega
  rw [NBL_ViewNatural.source proof semantic y1 size] at call
  cases decoded : NBL_ViewNatural.decoded proof size with
  | none =>
    rw [decoded] at call
    cases call
  | some value =>
    rw [decoded] at call
    have same := core.result.Result.Ok.inj (Result.ok.inj call)
    subst view
    have r0 := NBL_SlicePort.length proof 7527#usize 7751#usize (by decide) (by change 7751≤_;omega)
    have r1 := NBL_SlicePort.length proof 7783#usize 8007#usize (by decide) (by change 8007≤_;omega)
    have fm := NBL_SlicePort.length proof 8007#usize 10055#usize (by decide) (by change 10055≤_;omega)
    exact ⟨rfl,rfl,rfl,r0,r1,fm,⟨NBL_ViewProduct.root proof size,rfl,rfl⟩⟩

#print axioms source
end AspisR1.NBL_ViewDomains
