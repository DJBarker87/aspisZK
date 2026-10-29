import R1Z.PV_RDB2F_WordArray
namespace R1Z.PV_RDB2F_ByteArray
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Memory := Nat → Option U8
def Represents (n : Usize) (mem : Memory) (base : Nat) (current : Array U8 n) : Prop :=
  ∀ j : Usize, j.val<n.val → mem (base+j.val)=current.val[j.val]?
def store (mem : Memory) (ptr : Nat) (value : U8) : Memory :=
  fun a => if a=ptr then some value else mem a

theorem native_byte_store (n : Usize) (current : Array U8 n) (mem : Memory) (base : Nat)
    (i : Usize) (value : U8) (h : i.val<n.val) (rep : Represents n mem base current) :
    Represents n (store mem (base+i.val) value) base (current.set i value) := by
  intro j hj
  by_cases e : j.val=i.val
  · have read : (current.set i value).val[i.val]?=some value := by
      simp [Array.set,List.getElem?_set,h,current.property]
    simp only [store,show base+j.val=base+i.val by omega,if_true]
    simpa only [e] using read.symm
  · have frame : (current.set i value).val[j.val]?=current.val[j.val]? := by
      simp [Array.set,List.getElem?_set,e,Ne.symm e]
    simp only [store,show base+j.val≠base+i.val by omega,if_false,frame]
    exact rep j hj

/-- A write outside this byte leaves its address untouched, including disjoint
core fields and the caller's output/buffer allocations. -/
theorem other_allocation (mem : Memory) (ptr a : Nat) (value : U8) (ne : a≠ptr) :
    store mem ptr value a=mem a := by simp only [store,ne,if_false]

#print axioms native_byte_store
#print axioms other_allocation
end R1Z.PV_RDB2F_ByteArray
