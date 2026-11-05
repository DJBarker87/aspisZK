import NHS_PendingReservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_PendingStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativePendingBody
/-- Native K001 arbitrary observation window. Length and every untouched row
belong to the same after Vec; no whole-body output equality is a field. -/
structure Windows (raw after : alloc.vec.Vec Row) (index next : Usize)
 (w : aspis_core.field.QM31) : Prop where
 size : after.val.length=64
 increment : next.val=index.val+1
 rows : ∀ j : Nat, j<64 → after.val[j]?=
   if j=index.val then some (Port3_PendingInstall.row w) else raw.val[j]?

theorem same_vec (raw after : alloc.vec.Vec Row) (index next : Usize)
 (w : aspis_core.field.QM31) (size : raw.val.length=64) (active : index.val<64)
 (windows : Windows raw after index next w) : after=raw.set index (Port3_PendingInstall.row w) := by
 have afterSize := windows.size
 apply Subtype.ext
 change after.val=raw.val.set index.val (Port3_PendingInstall.row w)
 apply List.ext_getElem?
 intro j
 by_cases bound : j<64
 · rw [windows.rows j bound]
   by_cases same : j=index.val
   · subst j
     rw [if_pos rfl,List.getElem?_set_self (by omega)]
   · rw [if_neg same,List.getElem?_set_ne (Ne.symm same)]
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by simpa using (show raw.val.length≤j by omega))]

/-- SAME logged after-state receives the emitted one-iteration equation. -/
theorem source (weights : Slice aspis_core.field.QM31) (raw after : alloc.vec.Vec Row)
 (index next : Usize) (w : aspis_core.field.QM31)
 (wsize : weights.val.length=64) (rsize : raw.val.length=64) (active : index.val<64)
 (read : Slice.index_usize weights index=ok w) (windows : Windows raw after index next w) :
 body weights raw index=ok (.cont (after,next)) := by
 obtain ⟨derived,readDerived,step⟩ := Port3_NativePendingStep.step weights raw index wsize rsize active
 have same := Result.ok.inj (readDerived.symm.trans read)
 subst derived
 have equal := same_vec raw after index next w rsize active windows
 have nextSame : Usize.wrapping_add index 1#usize=next := by
   apply UScalar.eq_of_val_eq
   rw [Port3_Wrapping.increment index (by omega),windows.increment]
 rw [←equal,nextSame] at step
 exact step
#print axioms same_vec
#print axioms source
end AspisR1.NHS_PendingStep
