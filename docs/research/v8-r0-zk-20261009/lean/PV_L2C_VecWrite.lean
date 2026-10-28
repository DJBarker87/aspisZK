import PV_L2C_VecRead
set_option autoImplicit false
namespace PV_L2C_VecWrite
open Aeneas Aeneas.Std Result PV_L2C_VecRead

theorem index_mut {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A)
    (r : Usize) (hr : r.val<n) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice A) (vector hn f) r=
      ok (f ⟨r.val,hr⟩, Slice.set (alloc.vec.Vec.deref (vector hn f)) r) := by
  change (do let x ← Slice.index_usize (alloc.vec.Vec.deref (vector hn f)) r
             ok (x,Slice.set (alloc.vec.Vec.deref (vector hn f)) r))=_
  rw [read hn f r hr]
  rfl
#print axioms index_mut

theorem write {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A)
    (r : Usize) (hr : r.val<n) (x : A) :
    Slice.set (alloc.vec.Vec.deref (vector hn f)) r x=
      vector hn (fun i => if i.val=r.val then x else f i) := by
  apply Subtype.ext
  simp only [Slice.set_val_eq,alloc.vec.Vec.deref,vector]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    by_cases h : i=r.val <;> simp [List.getElem_set,h,eq_comm]
#print axioms write
end PV_L2C_VecWrite
