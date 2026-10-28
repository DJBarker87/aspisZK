import NDO_JGk_TX2_ParentWrite
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_View
open Aeneas Aeneas.Std Result MultiproofConeRef
abbrev Digest := Array U8 32#usize

structure View (s : reference.Scratch) (indices : List U32) (values : List Digest) (cursor : Nat) : Prop where
  size : s.n.val=indices.length
  lengths : values.length=indices.length
  idx : s.idx.val.take indices.length=indices
  val : s.val.val.take indices.length=values
  at_eq : s.«at».val=cursor

theorem read {α : Type} (a : Array α 16#usize) (xs : List α) (front : a.val.take xs.length=xs)
    (i : Usize) (bound : i.val<xs.length) :
    Array.index_usize a i=ok (xs[i.val]'bound) := by
  have eq := congrArg (fun ys : List α => ys[i.val]?) front
  simp only [List.getElem?_take,if_pos bound] at eq
  simp only [Array.index_usize,Array.getElem?_Usize_eq,eq,List.getElem?_eq_getElem bound]
#print axioms read

theorem index (s : reference.Scratch) (xs : List U32) (ys : List Digest) (cursor : Nat)
    (view : View s xs ys cursor) (i : Usize) (bound : i.val<xs.length) :
    Array.index_usize s.idx i=ok (xs[i.val]'bound) := read s.idx xs view.idx i bound
#print axioms index

theorem value (s : reference.Scratch) (xs : List U32) (ys : List Digest) (cursor : Nat)
    (view : View s xs ys cursor) (i : Usize) (bound : i.val<ys.length) :
    Array.index_usize s.val i=ok (ys[i.val]'bound) := by
  exact read s.val ys (by simpa only [view.lengths] using view.val) i bound
#print axioms value

theorem after (s : reference.Scratch) (xs : List U32) (ys : List Digest) (cursor : Nat)
    (view : View s xs ys cursor) (index : U32) (w : Usize) (digest : Digest) (next : Usize)
    (bound : w.val<xs.length) :
    View (JGk_TX2_ParentWrite.after s index w digest next)
      (xs.set w.val (JGk_TX2_ParentWrite.parentIndex index)) (ys.set w.val digest) next.val := by
  refine ⟨?_,?_,?_,?_,rfl⟩
  · simpa only [JGk_TX2_ParentWrite.after,List.length_set] using view.size
  · simpa only [List.length_set] using view.lengths
  · simp only [JGk_TX2_ParentWrite.after,Array.set_val_eq,List.length_set,List.take_set,view.idx]
  · simp only [JGk_TX2_ParentWrite.after,Array.set_val_eq,List.length_set,List.take_set,view.val]
#print axioms after

/-- Complete a level by reducing the live prefix and setting its new count. -/
theorem finish (s : reference.Scratch) (xs : List U32) (ys : List Digest) (cursor : Nat)
    (view : View s xs ys cursor) (n : Usize) (small : n.val≤xs.length) :
    View {s with n:=n} (xs.take n.val) (ys.take n.val) cursor := by
  have il : (xs.take n.val).length=n.val := by rw [List.length_take,Nat.min_eq_left small]
  refine ⟨il.symm,?_,?_,?_,view.at_eq⟩
  · simp only [List.length_take,view.lengths]
  · have eq := congrArg (List.take n.val) view.idx
    simpa only [il,List.take_take,Nat.min_eq_left small] using eq
  · have eq := congrArg (List.take n.val) view.val
    simpa only [il,List.take_take,Nat.min_eq_left small] using eq
#print axioms finish
end AspisR1.JGm_TX2_View
end
