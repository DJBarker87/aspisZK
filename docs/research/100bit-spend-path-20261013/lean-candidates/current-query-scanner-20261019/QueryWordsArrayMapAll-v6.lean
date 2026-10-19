import QueryScanMapStateAll
import AspisR1QueryScan.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled

theorem array_map_success_all {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U)
    (P : U → Prop)
    (hcall : ∀ f x y f', callback.call_mut f x = .ok (y, f') → P y)
    (self : Array T N) (f : F) (out : Array U N)
    (hm : core.array.Array.map callback self f = .ok out) :
    ∀ y ∈ out.val, P y := by
  unfold AspisR1QueryScanUnrolled.core.array.Array.map at hm
  unfold AspisR1SelectedMaskProbe.core.array.Array.map at hm
  unfold Aeneas.Std.core.array.Array.map at hm
  split at hm
  · rename_i ys last hstate
    have heq := Result.ok.inj hm
    have hout : (out : List U) = ys := by
      have hval := congrArg (fun z : Array U N => (z : List U)) heq
      exact hval.symm
    have hprop : ∀ y ∈ ys, P y := mapState_all callback.call_mut P hcall self.val f ys last hstate
    intro y hy
    rw [hout] at hy
    exact hprop y hy
  · simp_all
  · simp_all

end AspisR1QueryScanUnrolled
