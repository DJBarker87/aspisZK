import AspisR1CoinEffect27.Funs
import R1Z.ProverCommitCoinTape27
import R1Z.ProverCommitOwnedBytes
/-! The newly extracted explicit-state operation. No old pure dictionary is
reclassified as effectful. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitExtractedCoin27
open Aeneas Aeneas.Std Result AspisR1CoinEffect27
open ProverCommitOwnedDecoder
attribute [local instance] Classical.propDecidable
abbrev Bytes32 := Array U8 32#usize
local instance : DecidableEq Bytes32 := Classical.decEq _

theorem bytes_ext (a b : Bytes32) (h : ∀ i, byteAt a i = byteAt b i) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro i ha hb
    exact h ⟨i,by have := a.property; change a.val.length=32 at this; omega⟩

theorem bytes_eq_iff (a b : Bytes32) : a=b ↔
    byteAt a ⟨0,by decide⟩ = byteAt b ⟨0,by decide⟩ ∧
    byteAt a ⟨1,by decide⟩ = byteAt b ⟨1,by decide⟩ ∧
    byteAt a ⟨2,by decide⟩ = byteAt b ⟨2,by decide⟩ ∧
    byteAt a ⟨3,by decide⟩ = byteAt b ⟨3,by decide⟩ ∧
    byteAt a ⟨4,by decide⟩ = byteAt b ⟨4,by decide⟩ ∧
    byteAt a ⟨5,by decide⟩ = byteAt b ⟨5,by decide⟩ ∧
    byteAt a ⟨6,by decide⟩ = byteAt b ⟨6,by decide⟩ ∧
    byteAt a ⟨7,by decide⟩ = byteAt b ⟨7,by decide⟩ ∧
    byteAt a ⟨8,by decide⟩ = byteAt b ⟨8,by decide⟩ ∧
    byteAt a ⟨9,by decide⟩ = byteAt b ⟨9,by decide⟩ ∧
    byteAt a ⟨10,by decide⟩ = byteAt b ⟨10,by decide⟩ ∧
    byteAt a ⟨11,by decide⟩ = byteAt b ⟨11,by decide⟩ ∧
    byteAt a ⟨12,by decide⟩ = byteAt b ⟨12,by decide⟩ ∧
    byteAt a ⟨13,by decide⟩ = byteAt b ⟨13,by decide⟩ ∧
    byteAt a ⟨14,by decide⟩ = byteAt b ⟨14,by decide⟩ ∧
    byteAt a ⟨15,by decide⟩ = byteAt b ⟨15,by decide⟩ ∧
    byteAt a ⟨16,by decide⟩ = byteAt b ⟨16,by decide⟩ ∧
    byteAt a ⟨17,by decide⟩ = byteAt b ⟨17,by decide⟩ ∧
    byteAt a ⟨18,by decide⟩ = byteAt b ⟨18,by decide⟩ ∧
    byteAt a ⟨19,by decide⟩ = byteAt b ⟨19,by decide⟩ ∧
    byteAt a ⟨20,by decide⟩ = byteAt b ⟨20,by decide⟩ ∧
    byteAt a ⟨21,by decide⟩ = byteAt b ⟨21,by decide⟩ ∧
    byteAt a ⟨22,by decide⟩ = byteAt b ⟨22,by decide⟩ ∧
    byteAt a ⟨23,by decide⟩ = byteAt b ⟨23,by decide⟩ ∧
    byteAt a ⟨24,by decide⟩ = byteAt b ⟨24,by decide⟩ ∧
    byteAt a ⟨25,by decide⟩ = byteAt b ⟨25,by decide⟩ ∧
    byteAt a ⟨26,by decide⟩ = byteAt b ⟨26,by decide⟩ ∧
    byteAt a ⟨27,by decide⟩ = byteAt b ⟨27,by decide⟩ ∧
    byteAt a ⟨28,by decide⟩ = byteAt b ⟨28,by decide⟩ ∧
    byteAt a ⟨29,by decide⟩ = byteAt b ⟨29,by decide⟩ ∧
    byteAt a ⟨30,by decide⟩ = byteAt b ⟨30,by decide⟩ ∧
    byteAt a ⟨31,by decide⟩ = byteAt b ⟨31,by decide⟩ := by
  constructor
  · intro h; subst b; simp
  · intro h
    rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31⟩
    apply bytes_ext
    intro i
    fin_cases i <;> assumption


theorem byte_bne (a b : U8) : (a != b) = decide (a≠b) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem different0_eq (a b : Bytes32) : different0 a b = ok (decide (¬(
    byteAt a ⟨0,by decide⟩ = byteAt b ⟨0,by decide⟩ ∧
    byteAt a ⟨1,by decide⟩ = byteAt b ⟨1,by decide⟩ ∧
    byteAt a ⟨2,by decide⟩ = byteAt b ⟨2,by decide⟩ ∧
    byteAt a ⟨3,by decide⟩ = byteAt b ⟨3,by decide⟩ ∧
    byteAt a ⟨4,by decide⟩ = byteAt b ⟨4,by decide⟩ ∧
    byteAt a ⟨5,by decide⟩ = byteAt b ⟨5,by decide⟩ ∧
    byteAt a ⟨6,by decide⟩ = byteAt b ⟨6,by decide⟩ ∧
    byteAt a ⟨7,by decide⟩ = byteAt b ⟨7,by decide⟩))) := by
  unfold different0
  simp only [index_byteAt a 0#usize (by decide), index_byteAt b 0#usize (by decide),
    index_byteAt a 1#usize (by decide), index_byteAt b 1#usize (by decide),
    index_byteAt a 2#usize (by decide), index_byteAt b 2#usize (by decide),
    index_byteAt a 3#usize (by decide), index_byteAt b 3#usize (by decide),
    index_byteAt a 4#usize (by decide), index_byteAt b 4#usize (by decide),
    index_byteAt a 5#usize (by decide), index_byteAt b 5#usize (by decide),
    index_byteAt a 6#usize (by decide), index_byteAt b 6#usize (by decide),
    index_byteAt a 7#usize (by decide), index_byteAt b 7#usize (by decide),bind_tc_ok]
  split_ifs <;> simp_all [byte_bne,UScalar.eq_equiv]

theorem different8_eq (a b : Bytes32) : different8 a b = ok (decide (¬(
    byteAt a ⟨8,by decide⟩ = byteAt b ⟨8,by decide⟩ ∧
    byteAt a ⟨9,by decide⟩ = byteAt b ⟨9,by decide⟩ ∧
    byteAt a ⟨10,by decide⟩ = byteAt b ⟨10,by decide⟩ ∧
    byteAt a ⟨11,by decide⟩ = byteAt b ⟨11,by decide⟩ ∧
    byteAt a ⟨12,by decide⟩ = byteAt b ⟨12,by decide⟩ ∧
    byteAt a ⟨13,by decide⟩ = byteAt b ⟨13,by decide⟩ ∧
    byteAt a ⟨14,by decide⟩ = byteAt b ⟨14,by decide⟩ ∧
    byteAt a ⟨15,by decide⟩ = byteAt b ⟨15,by decide⟩))) := by
  unfold different8
  simp only [index_byteAt a 8#usize (by decide), index_byteAt b 8#usize (by decide),
    index_byteAt a 9#usize (by decide), index_byteAt b 9#usize (by decide),
    index_byteAt a 10#usize (by decide), index_byteAt b 10#usize (by decide),
    index_byteAt a 11#usize (by decide), index_byteAt b 11#usize (by decide),
    index_byteAt a 12#usize (by decide), index_byteAt b 12#usize (by decide),
    index_byteAt a 13#usize (by decide), index_byteAt b 13#usize (by decide),
    index_byteAt a 14#usize (by decide), index_byteAt b 14#usize (by decide),
    index_byteAt a 15#usize (by decide), index_byteAt b 15#usize (by decide),bind_tc_ok]
  split_ifs <;> simp_all [byte_bne,UScalar.eq_equiv]

theorem different16_eq (a b : Bytes32) : different16 a b = ok (decide (¬(
    byteAt a ⟨16,by decide⟩ = byteAt b ⟨16,by decide⟩ ∧
    byteAt a ⟨17,by decide⟩ = byteAt b ⟨17,by decide⟩ ∧
    byteAt a ⟨18,by decide⟩ = byteAt b ⟨18,by decide⟩ ∧
    byteAt a ⟨19,by decide⟩ = byteAt b ⟨19,by decide⟩ ∧
    byteAt a ⟨20,by decide⟩ = byteAt b ⟨20,by decide⟩ ∧
    byteAt a ⟨21,by decide⟩ = byteAt b ⟨21,by decide⟩ ∧
    byteAt a ⟨22,by decide⟩ = byteAt b ⟨22,by decide⟩ ∧
    byteAt a ⟨23,by decide⟩ = byteAt b ⟨23,by decide⟩))) := by
  unfold different16
  simp only [index_byteAt a 16#usize (by decide), index_byteAt b 16#usize (by decide),
    index_byteAt a 17#usize (by decide), index_byteAt b 17#usize (by decide),
    index_byteAt a 18#usize (by decide), index_byteAt b 18#usize (by decide),
    index_byteAt a 19#usize (by decide), index_byteAt b 19#usize (by decide),
    index_byteAt a 20#usize (by decide), index_byteAt b 20#usize (by decide),
    index_byteAt a 21#usize (by decide), index_byteAt b 21#usize (by decide),
    index_byteAt a 22#usize (by decide), index_byteAt b 22#usize (by decide),
    index_byteAt a 23#usize (by decide), index_byteAt b 23#usize (by decide),bind_tc_ok]
  split_ifs <;> simp_all [byte_bne,UScalar.eq_equiv]

theorem different24_eq (a b : Bytes32) : different24 a b = ok (decide (¬(
    byteAt a ⟨24,by decide⟩ = byteAt b ⟨24,by decide⟩ ∧
    byteAt a ⟨25,by decide⟩ = byteAt b ⟨25,by decide⟩ ∧
    byteAt a ⟨26,by decide⟩ = byteAt b ⟨26,by decide⟩ ∧
    byteAt a ⟨27,by decide⟩ = byteAt b ⟨27,by decide⟩ ∧
    byteAt a ⟨28,by decide⟩ = byteAt b ⟨28,by decide⟩ ∧
    byteAt a ⟨29,by decide⟩ = byteAt b ⟨29,by decide⟩ ∧
    byteAt a ⟨30,by decide⟩ = byteAt b ⟨30,by decide⟩ ∧
    byteAt a ⟨31,by decide⟩ = byteAt b ⟨31,by decide⟩))) := by
  unfold different24
  simp only [index_byteAt a 24#usize (by decide), index_byteAt b 24#usize (by decide),
    index_byteAt a 25#usize (by decide), index_byteAt b 25#usize (by decide),
    index_byteAt a 26#usize (by decide), index_byteAt b 26#usize (by decide),
    index_byteAt a 27#usize (by decide), index_byteAt b 27#usize (by decide),
    index_byteAt a 28#usize (by decide), index_byteAt b 28#usize (by decide),
    index_byteAt a 29#usize (by decide), index_byteAt b 29#usize (by decide),
    index_byteAt a 30#usize (by decide), index_byteAt b 30#usize (by decide),
    index_byteAt a 31#usize (by decide), index_byteAt b 31#usize (by decide),bind_tc_ok]
  split_ifs <;> simp_all [byte_bne,UScalar.eq_equiv]

theorem or_result (a b : Bool) :
    (if a then (ok true : Result Bool) else ok b) = ok (a||b) := by
  cases a <;> rfl

theorem different_eq (a b : Bytes32) : different a b = ok (decide (a≠b)) := by
  simp only [different,different0_eq,different8_eq,different16_eq,different24_eq,
    bind_tc_ok,or_result]
  apply congrArg Result.ok
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true,decide_eq_true_eq,ne_eq,bytes_eq_iff,not_and_or]
  tauto

#print axioms bytes_ext
#print axioms bytes_eq_iff
#print axioms byte_bne
#print axioms or_result
#print axioms different0_eq
#print axioms different8_eq
#print axioms different16_eq
#print axioms different24_eq
#print axioms different_eq
end R1Z.ProverCommitExtractedCoin27
