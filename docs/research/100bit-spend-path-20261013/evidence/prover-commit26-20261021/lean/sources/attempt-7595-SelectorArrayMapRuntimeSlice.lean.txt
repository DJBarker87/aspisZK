import Aeneas.Std.Array.Array
import Aeneas.Std.Core.Ops

/-! Minimal exact declaration slice from AspisV8R19.TraversalRuntime for
state-threaded array mapping. The definitions are retained verbatim; the
unrelated quartic-field import and traversal models are omitted. -/
set_option autoImplicit false
namespace AspisV8R19.TraversalRuntime
open Aeneas Aeneas.Std Result

def mapState {T U F : Type} (call : F → T → Result (U × F)) :
    List T → F → Result (List U × F)
  | [], state => .ok ([],state)
  | x::xs, state => do
    let (y,state') ← call state x
    let (ys,state'') ← mapState call xs state'
    .ok (y::ys,state'')

theorem mapState_length {T U F : Type} (call : F → T → Result (U × F))
    (xs : List T) (state : F) (ys : List U) (last : F)
    (h : mapState call xs state = .ok (ys,last)) : ys.length = xs.length := by
  induction xs generalizing state ys last with
  | nil => simp [mapState] at h; rcases h with ⟨rfl,rfl⟩; rfl
  | cons x xs ih =>
    simp only [mapState] at h
    cases hc : call state x with
    | fail e => simp [hc] at h
    | div => simp [hc] at h
    | ok pair =>
      rcases pair with ⟨y,state'⟩
      cases hm : mapState call xs state' with
      | fail e => simp [hc,hm] at h
      | div => simp [hc,hm] at h
      | ok pair =>
        rcases pair with ⟨tail,state''⟩
        simp only [hc,hm,bind_tc_ok,Result.ok.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        simp only [List.length_cons,ih _ _ _ hm]

end AspisV8R19.TraversalRuntime

namespace Aeneas.Std
open Result AspisV8R19.TraversalRuntime

def core.array.Array.map {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U) (self : Array T N) (f : F) :
    Result (Array U N) :=
  match h : mapState callback.call_mut self.val f with
  | .ok (ys,_last) => .ok ⟨ys,(mapState_length _ _ _ _ _ h).trans self.property⟩
  | .fail e => .fail e
  | .div => .div

end Aeneas.Std
