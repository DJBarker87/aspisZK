-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPf_BaseMultiply
set_option autoImplicit false
namespace NBQ_QueryBounds
open Aeneas Aeneas.Std AspisR1
/-- All source offsets in all four slots are inside the same608-byte prefix. -/
theorem offsets (slot term : Nat) (hs : slot<4) (ht : term<26) :
    slot*120+term*4+4≤608 ∧ slot*120+104+16≤608 ∧
    480+slot*32+16≤608 ∧ 480+slot*32+16+16≤608 := by omega
/-- A four-term raw group fits u64 without any modular reduction. -/
theorem product (a b : Nat) (ha : a<2147483647) (hb : b<2147483647) :
    a*b≤4611686009837453316 := by
  exact (Nat.mul_le_mul (show a≤2147483646 by omega) (show b≤2147483646 by omega))

theorem group_bound (s p : Nat) (k : Nat) (hk : k<4)
    (hs : s≤k*4611686009837453316) (hp : p≤4611686009837453316) :
    s+p≤(k+1)*4611686009837453316 ∧ s+p<18446744073709551616 := by omega
/-- Fold preserves residue and fits the stated seven-group accumulator bound. -/
theorem fold (s : Nat) (hs : s<18446744073709551616) :
    LPe_MersenneReduction.fold s≤10737418238 ∧
    LPe_MersenneReduction.fold s % 2147483647=s%2147483647 := by
  constructor
  · unfold LPe_MersenneReduction.fold; omega
  · exact LPe_MersenneReduction.fold_mod s

theorem folded_groups (s p : Nat) (k : Nat) (hk : k<7)
    (hs : s≤k*10737418238) (hp : p≤10737418238) :
    s+p≤(k+1)*10737418238 ∧ s+p<18446744073709551616 := by omega
#print axioms offsets
#print axioms product
#print axioms group_bound
#print axioms fold
#print axioms folded_groups
end NBQ_QueryBounds
