import R1Z.PV_RDB2F_RawHandles
namespace R1Z.PV_RDB2F_WordArray
open Aeneas Aeneas.Std Result PV_RDB2F_RawHandles
set_option autoImplicit false

def RepresentsN (n : Usize) (mem : Memory) (base : Nat) (current : Array U32 n) : Prop :=
  ∀ j : Usize, j.val<n.val → mem (address base j.val)=current.val[j.val]?

theorem readback (n : Usize) (current : Array U32 n) (i : Usize) (value : U32)
    (h : i.val<n.val) : (current.set i value).val[i.val]?=some value := by
  simp [Array.set,List.getElem?_set,h,current.property]

theorem other_words (n : Usize) (current : Array U32 n) (i j : Usize) (value : U32)
    (h : j.val≠i.val) : (current.set i value).val[j.val]?=current.val[j.val]? := by
  simp [Array.set,List.getElem?_set,h,Ne.symm h]

/-- Arbitrary array length, including soft::compress's sixteen mutable words. -/
theorem native_store (n : Usize) (current : Array U32 n) (mem : Memory) (base : Nat)
    (i : Usize) (value : U32) (h : i.val<n.val) (rep : RepresentsN n mem base current) :
    RepresentsN n (store mem (address base i.val) value) base (current.set i value) := by
  intro j hj
  by_cases e : j.val=i.val
  · have ptr : address base j.val=address base i.val := congrArg (address base) e
    rw [ptr,store_read]
    simpa only [e] using (readback n current i value h).symm
  · rw [store_frame mem _ _ value ((PV_RDB2E_PointerOffsets.injective base _ _).not.mpr e),
        other_words n current i j value e]
    exact rep j hj

#print axioms readback
#print axioms other_words
#print axioms native_store
end R1Z.PV_RDB2F_WordArray
