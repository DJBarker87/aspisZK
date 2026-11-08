import NNH_Tx2LiteralSlots
set_option autoImplicit false
namespace AspisR1.NNH_Run5bOffsets
open Aeneas Aeneas.Std Result
/-- Tiny offset arithmetic, using only the explicitly named irreducible constants. -/
theorem semantic : NHT_Constants.compact.COMPACT_SEMANTIC = (.ok 7015#usize : Result Usize) := by
 simp only [NHT_Constants.compact.COMPACT_SEMANTIC,NHT_Constants.compact.SEMANTIC_COMPACT_VALUES,
  NHT_Constants.compact.LOGICAL_SEMANTIC,NHT_Constants.verifier.SEMANTIC_BYTES]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]

theorem inactive : NHT_Constants.compact.OFF_INACTIVE = (.ok 7495#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_INACTIVE,NHT_Constants.compact.OFF_Y1,
  NHT_Constants.compact.OFF_SEMANTIC,NHT_Constants.compact.HEADER,
  NHT_Constants.compact.COMPACT_Y1,semantic]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]

theorem round0 : NHT_Constants.compact.OFF_ROUND0 = (.ok 7527#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_ROUND0,inactive]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]

theorem folded : NHT_Constants.compact.OFF_FOLDED_ROOT = (.ok 7751#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_FOLDED_ROOT,round0]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]

theorem round1 : NHT_Constants.compact.OFF_ROUND1 = (.ok 7783#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_ROUND1,folded]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]

theorem final : NHT_Constants.compact.OFF_FINAL = (.ok 8007#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_FINAL,round1]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]

theorem openings : NHT_Constants.compact.OFF_OPENINGS = (.ok 10055#usize : Result Usize) := by
 simp only [NHT_Constants.compact.OFF_OPENINGS,NHT_Constants.compact.FINAL_LEN,final]
 simp [UScalar.add, UScalar.mul, UScalar.sub, UScalar.tryMk]
#print axioms semantic
#print axioms inactive
#print axioms round0
#print axioms folded
#print axioms round1
#print axioms final
#print axioms openings
end AspisR1.NNH_Run5bOffsets
