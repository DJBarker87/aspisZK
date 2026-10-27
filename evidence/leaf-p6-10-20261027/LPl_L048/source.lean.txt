import LPl_ExpandFrame
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPl.Expand

def update (bs before : List U8) (row : Nat) : List U8 :=
  (List.range before.length).map (step bs before row)

theorem update_write (bs before : List U8) (row : Nat) :
    Write bs before (update bs before row) row := by
  constructor
  · simp only [update,List.length_map,List.length_range]
  · intro j hj; simp [update,hj]

theorem total (bs initial : List U8) (n : Nat) : ∃ after, Trace bs initial n after := by
  induction n with
  | zero => exact ⟨initial,.start⟩
  | succ n ih =>
    obtain ⟨before,h⟩ := ih
    exact ⟨update bs before n,.next n before (update bs before n) h (update_write bs before n)⟩

theorem output (bs initial after : List U8) (n : Nat)
    (trace : Trace bs initial n after) (done : 32*n=initial.length) :
    after=LPl_A.Expand.loop bs initial.length := by
  have hlen := length bs initial after n trace
  apply List.ext_getElem
  · rw [hlen,LPl_A.Expand.loop_length]
  · intro j hj hk
    have valid : j < initial.length := by omega
    have observed := invariant bs initial after n trace j valid
    rw [if_pos (by omega)] at observed
    have model : (LPl_A.Expand.loop bs initial.length)[j] = LPl_A.Expand.byte bs j := by
      simp only [LPl_A.Expand.loop_eq_map,List.getElem_map,List.getElem_range]
    rw [model]
    simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using observed

theorem unique (bs initial a b : List U8) (n : Nat)
    (done : 32*n=initial.length) (left : Trace bs initial n a) (right : Trace bs initial n b) : a=b :=
  (output bs initial a n left done).trans (output bs initial b n right done).symm

#print axioms update_write
#print axioms total
#print axioms output
#print axioms unique
end LPl.Expand
