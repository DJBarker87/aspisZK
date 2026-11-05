import NIS_SdkWriteFrame
set_option autoImplicit false
namespace NIJ_SdkWriteLoop
open AspisR1.S2Trust

def copy {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8) (start : Nat) : Nat → Heap F
 | 0 => s
 | n+1 => writeAt (copy s g source start n) g (start+n) (source (start+n))

theorem contents {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8)
 (start n k : Nat) (inside : start≤k ∧ k<start+n) :
 ((copy s g source start n).payload g.cell).contents k=source k := by
 induction n with
 | zero => omega
 | succ n ih =>
   by_cases last : k=start+n
   · subst k
     exact NIJ_SdkWriteFrame.byte _ _ _ _
   · have old : start≤k ∧ k<start+n := by omega
     change ((writeAt (copy s g source start n) g (start+n) (source (start+n))).payload g.cell).contents k=_
     rw [NIJ_SdkWriteFrame.other_byte _ _ _ _ _ last]
     exact ih old

theorem outside {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8)
 (start n k : Nat) (separate : k<start ∨ start+n≤k) :
 ((copy s g source start n).payload g.cell).contents k=(s.payload g.cell).contents k := by
 induction n with
 | zero => rfl
 | succ n ih =>
   have different : k≠start+n := by omega
   change ((writeAt (copy s g source start n) g (start+n) (source (start+n))).payload g.cell).contents k=_
   rw [NIJ_SdkWriteFrame.other_byte _ _ _ _ _ different]
   exact ih (by omega)

theorem other_cell {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8)
 (start n cell : Nat) (separate : cell≠g.cell) :
 (copy s g source start n).payload cell=s.payload cell := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [copy,NIJ_SdkWriteFrame.other_cell _ _ _ _ _ separate,ih]

theorem descriptor {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8)
 (start n cell : Nat) :
 ((copy s g source start n).payload cell).descriptor=(s.payload cell).descriptor := by
 induction n with
 | zero => rfl
 | succ n ih => rw [copy,NIJ_SdkWriteFrame.descriptor,ih]

theorem valid {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8)
 (start n : Nat) (before : Valid s) : Valid (copy s g source start n) := by
 induction n with
 | zero => exact before
 | succ n ih => exact NIJ_SdkWriteFrame.valid _ _ _ _ ih

#print axioms contents
#print axioms outside
#print axioms other_cell
#print axioms descriptor
#print axioms valid
end NIJ_SdkWriteLoop
