import Aeneas
import KMX_CopyMeaning
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace PCF_SliceFrame

def view {α : Type} [Inhabited α] (s : Slice α) : Nat → α := fun k => s.val[k]!

theorem length {α : Type} (s : Slice α) (base : Nat) (src : List α) :
    (s.setSlice! base src).length = s.length := by
  simp [Slice.setSlice!, Slice.length]

theorem window {α : Type} [Inhabited α] (s : Slice α) (base : Nat) (src : List α)
    (fits : base + src.length ≤ s.length) :
    view (s.setSlice! base src) =
      KMX_CopyMeaning.loop (fun k => src[k-base]!) (view s) base src.length := by
  funext k
  rw [KMX_CopyMeaning.loop_spec]
  by_cases inside : base ≤ k ∧ k < base + src.length
  · rw [if_pos inside]
    exact Slice.setSlice!_getElem!_middle s src base k ⟨inside.1,by omega,by omega⟩
  · rw [if_neg inside]
    have outside : k < base ∨ base + src.length ≤ k := by omega
    rcases outside with before | after
    · exact Slice.setSlice!_getElem!_prefix s src base k before
    · exact Slice.setSlice!_getElem!_suffix s src base k after

#print axioms length
#print axioms window
end PCF_SliceFrame
