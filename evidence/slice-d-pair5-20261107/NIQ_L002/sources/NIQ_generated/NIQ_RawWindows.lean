import NIG_FinishInput
set_option autoImplicit false
namespace NIQ_RawWindows
open Aeneas Aeneas.Std

/-- Exactly the byte window consumed by weights::field, before decoding. -/
def cell (bytes : Slice U8) (i : Nat) : List U8 :=
 (bytes.val.drop (32*i)).take 32

theorem byte (bytes : Slice U8) (i j : Nat) (small : j < 32) :
 (cell bytes i)[j]? = bytes.val[32*i+j]? := by
 simp only [cell, List.getElem?_take_of_lt small, List.getElem?_drop]

theorem word (bytes : Slice U8) (i j : Nat) (small : j < 8) :
 NIG_FinishInput.word (cell bytes i) (4*j) =
 NIG_FinishInput.word bytes.val (32*i+4*j) := by
 unfold NIG_FinishInput.word
 rw [byte bytes i (4*j) (by omega), byte bytes i (4*j+1) (by omega),
  byte bytes i (4*j+2) (by omega), byte bytes i (4*j+3) (by omega)]
 simp only [Nat.add_assoc]

theorem length (bytes : Slice U8) (n i : Nat)
 (windows : NIG_FinishInput.Windows bytes n) (small : i < n) :
 (cell bytes i).length = 32 := by
 simp only [cell, List.length_take, List.length_drop, windows.1]
 omega

/-- The primitive domain is transported from the SAME bytes, with no field
reply or successful pair hypothesis. -/
theorem canonical (bytes : Slice U8) (n i j : Nat)
 (windows : NIG_FinishInput.Windows bytes n) (cellSmall : i < n) (wordSmall : j < 8) :
 NIG_FinishInput.word (cell bytes i) (4*j) < 2147483647 := by
 rw [word bytes i j wordSmall]
 exact windows.2 i cellSmall j wordSmall

theorem range (bytes : Slice U8) (n i : Nat)
 (windows : NIG_FinishInput.Windows bytes n) (small : i < n) :
 32*(i+1) <= bytes.val.length := by
 rw [windows.1]
 omega

#print axioms byte
#print axioms word
#print axioms length
#print axioms canonical
#print axioms range
end NIQ_RawWindows
