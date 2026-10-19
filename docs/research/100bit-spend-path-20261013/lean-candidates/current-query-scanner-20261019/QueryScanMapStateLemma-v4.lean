import QueryScanMapStateLemma
import AspisR1QueryScan.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled

theorem mapState_all {T U F : Type}
    (call : F → T → Result (U × F)) (P : U → Prop)
    (hcall : ∀ f x y f', call f x = .ok (y, f') → P y)
    (xs : List T) (state : F) (ys : List U) (state' : F)
    (hm : AspisV8R19.TraversalRuntime.mapState call xs state = .ok (ys, state')) :
    ∀ y ∈ ys, P y := by
  induction xs generalizing state ys state' with
  | nil =>
      simp [AspisV8R19.TraversalRuntime.mapState] at hm
      rcases hm with ⟨hys, hstate⟩
      subst ys
      subst state'
      simp
  | cons x xs ih =>
      rw [mapState_cons call x xs state] at hm
      cases hfirst : call state x with
      | fail e => simp [hfirst] at hm
      | div => simp [hfirst] at hm
      | ok p =>
          rcases p with ⟨y, state1⟩
          have hy : P y := hcall state x y state1 hfirst
          cases htail : AspisV8R19.TraversalRuntime.mapState call xs state1 with
          | fail e => simp [hfirst, htail] at hm
          | div => simp [hfirst, htail] at hm
          | ok p2 =>
              rcases p2 with ⟨ys2, state2⟩
              simp [hfirst, htail] at hm
              rcases hm with ⟨hys, hstate⟩
              subst ys
              subst state'
              intro z hz
              simp only [List.mem_cons] at hz
              rcases hz with hz | hz
              · subst z
                exact hy
              · exact ih state1 ys2 state2 htail z hz

#print axioms mapState_all
end AspisR1QueryScanUnrolled
