import S2H_CutRelation
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2Trust S2E S2E_Reference.S2E_Reference

def setCounter (sdk : SDK) (slot : Usize) (cell : OwnedDataCell) (next : Isize) : SDK :=
  {sdk with data_cells := alloc.vec.Vec.set sdk.data_cells slot {cell with borrowed := next}}

/-- Unbounded heap representation survives a single counter update. ALL bytes,
Rc counts, account fields, lamports and allocation identities are retained.
The two counters agree arithmetically; no native caller success is assumed. -/
theorem image_counter_update {Child Alloc Event : Type} (m : AllocationMap)
    (h : Heap (World Child Alloc Event)) (sdk : SDK) (image : HeapImage m h sdk)
    (slot : Usize) (cell : OwnedDataCell) (next : Isize)
    (read : sdk.data_cells.val[slot.val]? = some cell) :
    HeapImage m {h with counter := put h.counter (m.dataCell slot.val) next.val}
      (setCounter sdk slot cell next) := by
  have valid := (List.getElem?_eq_some_iff.mp read).1
  refine ⟨image.accounts,image.lamports,image.handles,?_,?_⟩
  · intro other updated fetched
    by_cases equal : slot.val = other
    · subst other
      have actual : updated = {cell with borrowed := next} := by
        have changed : (setCounter sdk slot cell next).data_cells.val[slot.val]? =
            some {cell with borrowed := next} := by
          simp only [setCounter,alloc.vec.Vec.set,List.getElem?_set_self valid]
        exact Option.some.inj (fetched.symm.trans changed)
      subst updated
      have before := image.data slot.val cell read
      refine ⟨before.1,before.2.1,before.2.2.1,?_,before.2.2.2.2.1,
        before.2.2.2.2.2.1,before.2.2.2.2.2.2⟩
      simp only [put,↓reduceIte]
    · have unchanged : sdk.data_cells.val[other]? = some updated := by
        simpa only [setCounter,alloc.vec.Vec.set,List.getElem?_set,if_neg equal] using fetched
      have before := image.data other updated unchanged
      have distinct : m.dataCell other ≠ m.dataCell slot.val := by
        intro same
        exact equal (m.dataInjective same).symm
      refine ⟨before.1,before.2.1,before.2.2.1,?_,before.2.2.2.2.1,
        before.2.2.2.2.2.1,before.2.2.2.2.2.2⟩
      simpa only [put,if_neg distinct] using before.2.2.2.1
  · intro i account fetched
    have bounds := image.slots i account fetched
    exact ⟨by simpa only [setCounter,alloc.vec.Vec.set,List.length_set] using bounds.1,bounds.2⟩

/-- Successful shared acquisition changes precisely the represented counter.
This law has no finite payload-size bound and retains the entire ambient state. -/
theorem image_shared_acquire {Child Alloc Event : Type} (m : AllocationMap)
    (h : Heap (World Child Alloc Event)) (sdk : SDK) (image : HeapImage m h sdk)
    (slot : Usize) (cell : OwnedDataCell) (next : Isize) (token owner : Nat)
    (read : sdk.data_cells.val[slot.val]? = some cell)
    (increment : next.val = cell.borrowed.val + 1) :
    HeapImage m (acquire h (m.dataCell slot.val) token owner .shared)
      (setCounter sdk slot cell next) := by
  have counter := (image.data slot.val cell read).2.2.2.1
  have update := image_counter_update m h sdk image slot cell next read
  refine ⟨update.accounts,update.lamports,update.handles,?_,update.slots⟩
  simpa only [acquire,↓reduceIte,counter,← increment] using update.data

/-- Exclusive acquire is the same full-allocation law with counter -1. -/
theorem image_exclusive_acquire {Child Alloc Event : Type} (m : AllocationMap)
    (h : Heap (World Child Alloc Event)) (sdk : SDK) (image : HeapImage m h sdk)
    (slot : Usize) (cell : OwnedDataCell) (token owner : Nat)
    (read : sdk.data_cells.val[slot.val]? = some cell) :
    HeapImage m (acquire h (m.dataCell slot.val) token owner .exclusive)
      (setCounter sdk slot cell (-1)#isize) := by
  have update := image_counter_update m h sdk image slot cell (-1)#isize read
  refine ⟨update.accounts,update.lamports,update.handles,?_,update.slots⟩
  have different : Kind.exclusive ≠ Kind.shared := by intro same; cases same
  have minus : ((-1)#isize).val = (-1 : Int) := by scalar_tac
  simpa only [acquire,if_neg different,minus] using update.data

#print axioms image_counter_update
#print axioms image_shared_acquire
#print axioms image_exclusive_acquire
end AspisR1.S2H
