import LPk_Induction
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace LPk_Result
open AspisR1.SamplerMachineBounds AspisR1.SamplerWordPass
open AspisR1.SamplerRepeatedPass AspisR1.SamplerPass
open AspisR1.ExtractedQM31SamplerPassLoop AspisR1.SourceSamplerByteRank
open AspisR1GammaCaller.DigitsModel

/-- The low returned native limb is the complete remaining quotient when
its positional value is below one word. -/
theorem low_word (a : Array U32 8#usize)
    (hs : wordValue (words a).reverse < B) :
    (a.val[0]'(by rw [a.property]; decide)).val = wordValue (words a).reverse := by
  rcases a with ⟨xs,hlen⟩
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
    change x.val = wordValue ((x::xs).map decode32).reverse
    change wordValue ((x::xs).map decode32).reverse < B at hs
    have he : wordValue ((x::xs).map decode32).reverse =
        wordValue (xs.map decode32).reverse * B + x.val := by
      simp only [wordValue,numeral,List.map_cons,List.reverse_cons,
        List.map_append,List.map_cons,List.map_nil,List.foldl_append,
        List.foldl_cons,List.foldl_nil,decode32_val]
    have hm : wordValue ((x::xs).map decode32).reverse % B = x.val := by
      rw [he,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt x.bv.isLt]
    rw [Nat.mod_eq_of_lt hs] at hm
    exact hm.symm

theorem values_injective (xs ys : List U32)
    (h : xs.map UScalar.val = ys.map UScalar.val) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have he := List.cons.inj h
      have hxy : x = y := UScalar.eq_of_val_eq he.1
      subst y
      rw [ih ys he.2]

/-- Complete carrier join: the source-shaped step trace, byte decoder, digit
writeback and low-word return give exactly the cohort Result. Only the local
native-step relation and ordered traversal are needed to construct the trace;
no whole native/cohort Result equality is a hypothesis. -/
theorem native_result (block : Array U8 32#usize)
    (digits quotient : Array U32 8#usize)
    (trace : LPk_Induction.Digits 8 (AspisR1.SamplerBytePass.digits block)
      (values digits) (words quotient).reverse) :
    AspisR1Post25Sampler.sampler.low_base_p_digits block =
      ok (digits,quotient.val[0]'(by rw [quotient.property]; decide)) := by
  have ht := LPk_Induction.eight_digits trace
  obtain ⟨ds,q,he,hd,hq,hb,hcanon⟩ := LPk_Cohort.all_blocks block
  have hds : ds = digits := Subtype.ext (values_injective _ _ (hd.trans ht.1.symm))
  have hsmall : wordValue (words quotient).reverse < B := by
    have hB : 256 < B := by norm_num [B]
    omega
  have hqeq : q = quotient.val[0]'(by rw [quotient.property]; decide) := by
    apply UScalar.eq_of_val_eq
    rw [low_word quotient hsmall]
    exact hq.trans ht.2.1.symm
  rw [hds,hqeq] at he
  exact he
#print axioms low_word
#print axioms values_injective
#print axioms native_result
end LPk_Result
