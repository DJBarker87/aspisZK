import NGO_ValidatorWord
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ValidatorWindows
def block (bytes : List U8) (i : Nat) (fitting : i+4≤bytes.length) : Array U8 4#usize :=
  Array.make 4#usize [bytes[i]'(by omega),bytes[i+1]'(by omega),
    bytes[i+2]'(by omega),bytes[i+3]'(by omega)]
/-- No substitute bytes: every natural word window is the original four
consecutive source bytes. -/
theorem window (bytes : List U8) (i : Nat) (fitting : i+4≤bytes.length) :
    (bytes.drop i).take 4=(block bytes i fitting).val := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,block,Array.make,List.length_cons,List.length_nil]
    omega
  · intro j hj hk
    have small : j<4 := by simpa only [block,Array.make,List.length_cons,List.length_nil] using hk
    interval_cases j <;> simp [block,Array.make,Nat.add_assoc]
theorem word (bytes : List U8) (i : Nat) (fitting : i+4≤bytes.length) :
    NFU_Retarget.LPl_Kit_Bytes.le32 ((bytes.drop i).take 4)=
      (core.num.U32.from_le_bytes (block bytes i fitting)).val := by
  rw [window bytes i fitting]
  exact NGO_ValidatorWord.le32 _ _ _ _
#print axioms window
#print axioms word
end NGO_ValidatorWindows
