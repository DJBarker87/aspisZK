import Aeneas
import AspisR1CuRho.Types

/-! Concrete standard-library models for the two external operations emitted
by the rho extraction. No opaque constant or custom axiom is introduced.
The mutable-array handback follows the existing traversal runtime. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CuRho

def mapState {T U F : Type} (call : F → T → Result (U × F)) :
    List T → F → Result (List U × F)
  | [], state => .ok ([], state)
  | x::xs, state => do
    let (y, state') ← call state x
    let (ys, state'') ← mapState call xs state'
    .ok (y::ys, state'')

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
      simp only [hc,bind_tc_ok] at h
      change (do
        let pair ← mapState call xs state'
        ok (y::pair.1,pair.2)) = ok (ys,last) at h
      cases hm : mapState call xs state' with
      | fail e => simp [hm] at h
      | div => simp [hm] at h
      | ok pair =>
        rcases pair with ⟨tail,state''⟩
        have hpair : (y::tail,state'') = (ys,last) := Result.ok.inj h
        have hys := congrArg Prod.fst hpair
        change y::tail = ys at hys
        rw [← hys,List.length_cons,ih _ _ _ hm]

def core.array.Array.map {T F U : Type} {N : Usize}
    (callback : core.ops.function.FnMut F T U) (self : Array T N) (f : F) :
    Result (Array U N) :=
  match h : mapState callback.call_mut self.val f with
  | .ok (ys,_) => .ok ⟨ys,(mapState_length _ _ _ _ _ h).trans self.property⟩
  | .fail e => .fail e
  | .div => .div

def MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
    {T : Type} {N : Usize} (array : Array T N) :
    Result (Aeneas.Std.core.slice.iter.IterMut T ×
      (Aeneas.Std.core.slice.iter.IterMut T → Array T N)) :=
  .ok ({ slice := Array.to_slice array },
    fun iterator => Array.from_slice array iterator.slice)

#print axioms mapState_length
#print axioms core.array.Array.map
#print axioms MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
end AspisR1CuRho
