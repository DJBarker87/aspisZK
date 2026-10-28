import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_ShaBranches
set_option autoImplicit false

theorem padding (pos : Nat) (h : pos<64) :
    (64-pos-1<8) ↔ ¬pos<56 := by omega

theorem suffix_fits : ¬(8>64) := by decide

theorem word_chunks : 32/4=8 ∧ 32%4=0 := by decide

theorem word_indices (i j : Nat) (hi : i<8) (hj : j<4) :
    4*i+j<32 ∧ (4*i+j)/4=i ∧ (4*i+j)%4=j := by omega

#print axioms padding
#print axioms suffix_fits
#print axioms word_chunks
#print axioms word_indices
end R1Z.PV_DL_ShaBranches
