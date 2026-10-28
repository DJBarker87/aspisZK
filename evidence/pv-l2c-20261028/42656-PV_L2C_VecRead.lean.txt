import R1Z.ProverCommitBalanceRecursion
set_option autoImplicit false
namespace PV_L2C_VecRead
open Aeneas Aeneas.Std Result

def vector {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A) : alloc.vec.Vec A :=
  ⟨List.ofFn f,by simpa only [List.length_ofFn] using hn⟩

theorem bound1024 : 1024≤Usize.max := by scalar_tac
#print axioms bound1024

theorem read {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A)
    (r : Usize) (hr : r.val<n) :
    Slice.index_usize (alloc.vec.Vec.deref (vector hn f)) r=ok (f ⟨r.val,hr⟩) := by
  unfold Slice.index_usize
  change (match (List.ofFn f)[r.val]? with
    | none => fail .arrayOutOfBounds
    | some x => ok x)=ok (f ⟨r.val,hr⟩)
  simp [hr]
#print axioms read

/-- The same literal row lookup for the public active array. -/
def active (f : Fin 1024 → Bool) : Aeneas.Std.Array Bool 1024#usize :=
  ⟨List.ofFn f,by simp⟩

theorem read_active (f : Fin 1024 → Bool) (r : Usize) (hr : r.val<1024) :
    Aeneas.Std.Array.index_usize (active f) r=ok (f ⟨r.val,hr⟩) := by
  unfold Aeneas.Std.Array.index_usize
  change (match (List.ofFn f)[r.val]? with
    | none => fail .arrayOutOfBounds
    | some x => ok x)=ok (f ⟨r.val,hr⟩)
  simp [hr]
#print axioms read_active

#print core.slice.index.SliceIndexUsizeSlice
end PV_L2C_VecRead
