import PCI_ValidateWords
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateCarrier
open PCI_ValidateWords

def readWord (x : U32) : UInt32 := UInt32.ofNat x.val

theorem read_word (x : UInt32) : readWord (word x)=x := by
  apply UInt32.toNat_inj.mp
  simp only [readWord,word_value,UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (UInt32.toNat_lt x)

theorem word_read (x : U32) : word (readWord x)=x := by
  apply UScalar.eq_of_val_eq
  have hx : x.val<4294967296 := by scalar_tac
  simp only [word_value,readWord,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hx]

theorem word_beq (x y : UInt32) : (word x == word y)=(x==y) := by
  by_cases h : x=y
  · subst y
    simp
  · have hw : word x≠word y := fun hh => h ((word_eq x y).mp hh)
    simp [h,hw]

theorem word_bne (x y : UInt32) : (word x != word y)=(x!=y) := by
  change (!(word x==word y))=(!(x==y))
  rw [word_beq]

theorem word_bne_zero (x : UInt32) : (word x != 0#u32)=(x!=0) := by
  change (word x != word (0:UInt32))=(x!=0)
  exact word_bne x 0

theorem word_eq_zero (x : UInt32) : word x=0#u32 ↔ x=0 := by
  change word x=word (0:UInt32) ↔ x=0
  exact word_eq x 0

theorem word_eq_one (x : UInt32) : word x=1#u32 ↔ x=1 := by
  change word x=word (1:UInt32) ↔ x=1
  exact word_eq x 1

theorem word_geP (x : UInt32) : word x>=2147483647#u32 ↔ x.toNat>=2147483647 := Iff.rfl

#print axioms read_word
#print axioms word_read
#print axioms word_beq
#print axioms word_bne
#print axioms word_bne_zero
#print axioms word_eq_zero
#print axioms word_eq_one
#print axioms word_geP
end PCI_ValidateCarrier
