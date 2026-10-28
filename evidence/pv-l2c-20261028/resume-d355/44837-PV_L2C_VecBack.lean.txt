import PV_L2C_VecWrite
set_option autoImplicit false
namespace PV_L2C_VecBack
open Aeneas Aeneas.Std Result PV_L2C_VecRead

/-- Name the Vec-typed restoration explicitly, retaining the write. -/
def back {A : Type} (v : alloc.vec.Vec A) (r : Usize) (x : A) : alloc.vec.Vec A :=
  ⟨(Slice.set (alloc.vec.Vec.deref v) r x).val,
    (Slice.set (alloc.vec.Vec.deref v) r x).property⟩

theorem index_mut {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A)
    (r : Usize) (hr : r.val<n) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice A) (vector hn f) r=
      ok (f ⟨r.val,hr⟩, back (vector hn f) r) := by
  change (do let x ← Slice.index_usize (alloc.vec.Vec.deref (vector hn f)) r
             ok (x,back (vector hn f) r))=_
  rw [read hn f r hr]
  rfl
#print axioms index_mut

theorem write {A : Type} {n : Nat} (hn : n≤Usize.max) (f : Fin n → A)
    (r : Usize) (hr : r.val<n) (x : A) :
    back (vector hn f) r x=vector hn (fun i => if i.val=r.val then x else f i) := by
  apply Subtype.ext
  exact congrArg Subtype.val (PV_L2C_VecWrite.write hn f r hr x)
#print axioms write
end PV_L2C_VecBack
