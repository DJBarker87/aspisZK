import R1Z.PV_RDCD4_Memory194
import R1Z.PV_RDCD4_Split194
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDCD4_MemorySplit194
open PV_RDCD4_Memory194
set_option autoImplicit false

def split {E : Type} (s : Span E) (mid : Nat) : Span E × Span E :=
  (sliceRawFromRawParts s.pointer mid,
   sliceRawFromRawParts (advance s.pointer mid) (s.len-mid))

theorem valid_parts {E : Type} (s : Span E) (mid : Nat)
    (hv : valid s.pointer s.len) (hm : mid ≤ s.len) :
    valid (split s mid).1.pointer (split s mid).1.len ∧
    valid (split s mid).2.pointer (split s mid).2.len := by
  simp only [split,sliceRawFromRawParts,ptrSliceFromRawParts,
    metadataFromRawParts,aggregate,advance,valid] at *
  constructor <;> omega

theorem left_values {E : Type} (s : Span E) (mid : Nat) (hm : mid ≤ s.len) :
    values (split s mid).1=(values s).take mid := by
  simp only [split,values,sliceRawFromRawParts,ptrSliceFromRawParts,
    metadataFromRawParts,aggregate,List.take_take,Nat.min_eq_left hm,Nat.min_eq_right hm]

theorem right_values {E : Type} (s : Span E) (mid : Nat) :
    values (split s mid).2=(values s).drop mid := by
  simp only [split,values,sliceRawFromRawParts,ptrSliceFromRawParts,
    metadataFromRawParts,aggregate,advance,List.drop_take,List.drop_drop,Nat.add_comm]

theorem partition {E : Type} (s : Span E) (mid : Nat) (hm : mid ≤ s.len) :
    values (split s mid).1 ++ values (split s mid).2=values s := by
  rw [left_values s mid hm,right_values,List.take_append_drop]

/-- The same logical backing region is retained; the second pointer advances
by exactly mid elements. This is not a machine-address observation theorem. -/
theorem aliases {E : Type} (s : Span E) (mid : Nat) :
    (split s mid).1.pointer=s.pointer ∧
    (split s mid).2.pointer.origin=s.pointer.origin ∧
    (split s mid).2.pointer.data=s.pointer.data ∧
    (split s mid).2.pointer.offset=s.pointer.offset+mid := ⟨rfl,rfl,rfl,rfl⟩

def checked {E : Type} (s : Span E) (mid : Nat) : Option (Span E × Span E) :=
  if mid ≤ s.len then some (split s mid) else none

theorem checked_binding {E : Type} (s : Span E) (mid : Nat)
    (hv : valid s.pointer s.len) :
    (checked s mid).map (fun p => (values p.1,values p.2))=
      PV_RDCD4_Split194.checked (values s) mid := by
  have hl : (values s).length=s.len := length s.pointer s.len hv
  by_cases hm : mid ≤ s.len
  · have h : mid ≤ (values s).length := by rw [hl]; exact hm
    simp only [checked,if_pos hm,Option.map_some,PV_RDCD4_Split194.checked,
      if_pos h,PV_RDCD4_Split194.unchecked]
    rw [left_values s mid hm,right_values]
  · have h : ¬mid ≤ (values s).length := by rw [hl]; exact hm
    simp only [checked,if_neg hm,Option.map_none,PV_RDCD4_Split194.checked,if_neg h]

#print axioms valid_parts
#print axioms left_values
#print axioms right_values
#print axioms partition
#print axioms aliases
#print axioms checked_binding
end R1Z.PV_RDCD4_MemorySplit194
