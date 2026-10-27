import LPl_Check
set_option autoImplicit false
namespace AspisR1.LPs_CheckDomain
open Aeneas Aeneas.Std Result

def byte (bs : List U8) (i : Nat) : Nat := (bs[i]?.getD 0#u8).val
def word (bs : List U8) (i : Nat) : Nat :=
  byte bs i + 256*byte bs (i+1) + 65536*byte bs (i+2) + 16777216*byte bs (i+3)
def CompactCanonical (bs : List U8) : Prop := ∀ row, row<29 → ∀ limb,
  limb<4 → word bs (16*row+4*limb)<2147483647

theorem byte_window (bs : List U8) (off width j : Nat) (hj : j<width) :
    byte ((bs.drop off).take width) j=byte bs (off+j) := by
  simp only [byte,List.getElem?_take,hj,↓reduceIte,List.getElem?_drop]

theorem word_window (bs : List U8) (off width j : Nat) (hj : j+3<width) :
    word ((bs.drop off).take width) j=word bs (off+j) := by
  simp only [word,byte_window bs off width j (by omega),
    byte_window bs off width (j+1) (by omega),
    byte_window bs off width (j+2) (by omega),
    byte_window bs off width (j+3) hj,Nat.add_assoc]

theorem echeck_word (bs : List U8) : LPl.Echeck.word bs=word bs 0 := by
  simp only [LPl.Echeck.word,LPl.Echeck.byte,word,byte,
    Nat.zero_add,Nat.mul_add]
  omega

theorem checked (compact : Slice U8) (len : compact.val.length=464)
    (success : _root_.compact.check_values compact=ok (.Ok ())) :
    CompactCanonical compact.val := by
  obtain ⟨out,trace⟩ := LPl.Check.total compact.val
  have call := LPl.Check.native_result compact out trace
  have none : out=none := by
    cases out <;> simp_all
  subst out
  have hit := LPl.Scan.first_error _ _ _ trace
  have good := (LPl_A.firstBad_none _ _).mp hit.symm
  intro row hr limb hl
  have count : row<compact.val.length/16 := by omega
  have row_good := good row count
  have chunk : LPl.Check.chunk ((compact.val.drop (16*row)).take 16)=true := by
    change (!LPl.Check.chunk _)=false at row_good
    cases h : LPl.Check.chunk ((compact.val.drop (16*row)).take 16) <;> simp_all
  have limbs := List.all_eq_true.mp chunk
  have bound := limbs limb (List.mem_range.mpr hl)
  change decide (LPl.Echeck.word _ < 2147483647)=true at bound
  have bound' := of_decide_eq_true bound
  rw [echeck_word,word_window _ (4*limb) 4 0 (by omega),Nat.add_zero,
    word_window _ (16*row) 16 (4*limb) (by omega)] at bound'
  exact bound'

#print axioms byte_window
#print axioms word_window
#print axioms echeck_word
#print axioms checked
end AspisR1.LPs_CheckDomain
