import LPt_LPl_A_ExpansionLaws
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace LPt_LPl_C.Expand
/-- Row/lane formulas for all caller rows, not a checked finite fixture. -/
theorem row_low (bs : List U8) (row lane : Nat) (lo : lane < 16) :
    LPt_LPl_A.Expand.byte bs (32*row+lane) = bs[16*row+lane]?.getD 0#u8 := by
  have div : (32*row+lane)/32 = row := by omega
  have mod : (32*row+lane)%32 = lane := by omega
  simp only [LPt_LPl_A.Expand.byte, mod, if_pos lo, div]
  congr 2 <;> omega
theorem row_high (bs : List U8) (row lane : Nat) (lo : 16 ≤ lane) (hi : lane < 32) :
    LPt_LPl_A.Expand.byte bs (32*row+lane) = 0#u8 := by
  have mod : (32*row+lane)%32 = lane := by omega
  simp only [LPt_LPl_A.Expand.byte, mod, if_neg (by omega : ¬ lane < 16)]
theorem caller_rows (bs : List U8) :
    (LPt_LPl_A.Expand.loop bs (29*32)).length = 928 := LPt_LPl_A.Expand.loop_length _ _
#print axioms row_low
#print axioms row_high
#print axioms caller_rows
end LPt_LPl_C.Expand
