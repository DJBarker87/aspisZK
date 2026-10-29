import NCJ_SliceCells
import NCJ_CallLog
set_option autoImplicit false
namespace NCJ_CellCanon
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def slice (s : Slice NQ) : Prop := ∀ x∈s.val,canonQ x
def array {n : Usize} (a : Array NQ n) : Prop := ∀ x∈a.val,canonQ x

theorem slice_read (s : Slice NQ) (i : Usize) (x : NQ) (h : slice s)
    (run : Slice.index_usize s i=ok x) : canonQ x := by
  unfold Slice.index_usize at run
  split at run
  · cases run
  · rename_i v read
    cases Result.ok.inj run
    exact h x (List.mem_of_getElem? read)

theorem array_read {n : Usize} (a : Array NQ n) (i : Usize) (x : NQ) (h : array a)
    (run : Array.index_usize a i=ok x) : canonQ x := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i v read
    cases Result.ok.inj run
    exact h x (List.mem_of_getElem? read)

theorem list_set {α : Type} (P : α → Prop) (xs : List α) (i : Nat) (v : α)
    (h : ∀ x∈xs,P x) (hv : P v) : ∀ x∈xs.set i v,P x := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    intro x hx
    cases i with
    | zero =>
      simp only [List.set,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact hv
      · exact h x (by simp [hx])
    | succ i =>
      simp only [List.set,List.mem_cons] at hx
      rcases hx with rfl|hx
      · exact h x (by simp)
      · exact ih i (fun x hx=>h x (by simp [hx])) x hx


theorem put (s : Slice NQ) (i : Nat) (v : NQ) (h : slice s) (hv : canonQ v) :
    slice (NCJ_SliceCells.put s i v) := list_set canonQ s.val i v h hv

#print axioms slice_read
#print axioms array_read
#print axioms list_set
#print axioms put
end NCJ_CellCanon
