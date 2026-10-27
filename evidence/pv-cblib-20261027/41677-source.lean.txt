import R1Z.PV_CBL_BufferInvariants
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PaddingBranch
set_option autoImplicit false
theorem branch (pos : Nat) (h : pos<64) : 64-pos-1<8 ↔ 56≤pos := by omega
theorem one_block (pos : Nat) (h : pos<56) : ¬64-pos-1<8 := by omega
theorem two_block (pos : Nat) (h : 56≤pos) (h64 : pos<64) : 64-pos-1<8 := by omega
theorem delimiter_bounds (pos : Nat) (h : pos<64) : pos+1≤64 := by omega
theorem suffix_start : 64-8=56 := rfl
#print axioms branch
#print axioms one_block
#print axioms two_block
#print axioms delimiter_bounds
#print axioms suffix_start
end R1Z.PV_CBL_PaddingBranch
