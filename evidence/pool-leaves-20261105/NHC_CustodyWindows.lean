import NGK_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NHC_CustodyWindows
/-- Exact slice geometry for the legacy token caller. Payload values and None/
Some tags remain arbitrary; this proves no parser or custody acceptance. -/
theorem window_length (bytes : List U8) (length : bytes.length = 165) (start width : Nat)
    (inside : start + width ≤ 165) : ((bytes.drop start).take width).length = width := by
  simp only [List.length_take,List.length_drop,length]
  exact Nat.min_eq_left (by omega)
#print axioms window_length

theorem token_options (bytes : List U8) (length : bytes.length = 165) :
    ((bytes.drop 72).take 36).length = 36 ∧
    ((bytes.drop 109).take 12).length = 12 ∧
    ((bytes.drop 129).take 36).length = 36 := by
  exact ⟨window_length bytes length 72 36 (by omega),
    window_length bytes length 109 12 (by omega),
    window_length bytes length 129 36 (by omega)⟩
#print axioms token_options

theorem mint_options (bytes : List U8) (length : bytes.length = 82) :
    (bytes.take 36).length = 36 ∧ (bytes.drop 46).length = 36 := by
  simp [List.length_take,List.length_drop,length]
#print axioms mint_options

theorem token_point (bytes : List U8) (start width j : Nat) (inside : j < width) :
    ((bytes.drop start).take width)[j]? = bytes[start+j]? := by
  simp [List.getElem?_take,List.getElem?_drop,inside,Nat.add_comm]
#print axioms token_point
end NHC_CustodyWindows
