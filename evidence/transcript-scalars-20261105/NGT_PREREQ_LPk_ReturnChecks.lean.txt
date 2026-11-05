import LPk_Constant
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace LPk_ReturnChecks
open AspisR1.SamplerMachineBounds AspisR1.SamplerWordPass
open AspisR1.SamplerRepeatedPass AspisR1.SamplerPass
open AspisR1.ExtractedQM31SamplerPassLoop AspisR1.SourceSamplerByteRank
open AspisR1GammaCaller.DigitsModel

theorem zero_words (xs : List UInt32) (h : wordValue xs = 0) :
    ∀ x ∈ xs, x.toNat = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have he : x.toNat * B^xs.length + wordValue xs = 0 := by
      simpa only [wordValue,List.map_cons,numeral_cons,List.length_map] using h
    have hp : x.toNat * B^xs.length = 0 := by omega
    have ht : wordValue xs = 0 := by omega
    have hx : x.toNat = 0 := by
      rcases Nat.mul_eq_zero.mp hp with hz | hz
      · exact hz
      · exact False.elim ((Nat.ne_of_gt (pow_pos B_pos xs.length)) hz)
    intro d hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d; exact hx
    · exact ih ht d hd

/-- The high-limb debug check follows from the full quotient value bound;
no native caller's high-limb success is supplied as a premise. -/
theorem high_zero (a : Array U32 8#usize)
    (hs : wordValue (words a).reverse < B) :
    ∀ x ∈ a.val.drop 1, x.val = 0 := by
  rcases a with ⟨xs,hlen⟩
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
    have he : wordValue ((x::xs).map decode32).reverse =
        wordValue (xs.map decode32).reverse * B + x.val := by
      simp only [wordValue,numeral,List.map_cons,List.reverse_cons,
        List.map_append,List.map_cons,List.map_nil,List.foldl_append,
        List.foldl_cons,List.foldl_nil,decode32_val]
    change wordValue ((x::xs).map decode32).reverse < B at hs
    rw [he] at hs
    have hz : wordValue (xs.map decode32).reverse = 0 := by
      by_contra hn
      have hp : 1 ≤ wordValue (xs.map decode32).reverse := by omega
      have hm := Nat.mul_le_mul_right B hp
      simp only [one_mul] at hm
      omega
    have hall := zero_words _ hz
    intro d hd
    have hmem : decode32 d ∈ (xs.map decode32).reverse := by
      apply List.mem_reverse.mpr
      exact List.mem_map.mpr ⟨d,by simpa using hd,rfl⟩
    simpa only [decode32_val] using hall (decode32 d) hmem

theorem checks (block : Array U8 32#usize) (digits quotient : Array U32 8#usize)
    (trace : LPk_Induction.Digits 8 (AspisR1.SamplerBytePass.digits block)
      (values digits) (words quotient).reverse) :
    (∀ x ∈ quotient.val.drop 1, x.val = 0) ∧
    (quotient.val[0]'(by rw [quotient.property]; decide)).val ≤ 256 := by
  have ht := LPk_Induction.eight_digits trace
  have hs : wordValue (words quotient).reverse < B := by
    have hb : 256 < B := by norm_num [B]
    omega
  exact ⟨high_zero quotient hs,by rw [LPk_Result.low_word quotient hs]; exact ht.2.2⟩
#print axioms zero_words
#print axioms high_zero
#print axioms checks
end LPk_ReturnChecks
