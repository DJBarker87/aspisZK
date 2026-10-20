import GammaCallerDigitsModel
import IndexedCandidateOuterByteOutputSuccessV5
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GammaCaller.DigitsModel
open AspisR1 AspisR1.SamplerMachineBounds AspisR1.SamplerNatModel
open AspisR1.SamplerRepeatedPass AspisR1.SamplerPass
open AspisR1.SourceSamplerByteRank AspisR1.ExtractedQM31SamplerPassLoop
open AspisR1Post25Sampler

private theorem wordValue_reverse_cons (x : U32) (xs : List U32) :
    wordValue ((x :: xs).map decode32).reverse =
      wordValue (xs.map decode32).reverse * B + x.val := by
  simp only [wordValue, numeral, List.map_cons, List.reverse_cons,
    List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil, decode32_val]

private theorem low_word_of_small_value (arr : Array U32 8#usize)
    (hsmall : wordValue (words arr).reverse < B) :
    (arr.val[0]'(by rw [arr.property]; decide)).val = wordValue (words arr).reverse := by
  rcases arr with ⟨xs,hlen⟩
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
      change x.val = wordValue ((x :: xs).map decode32).reverse
      change wordValue ((x :: xs).map decode32).reverse < B at hsmall
      have hx : x.val < B := x.bv.isLt
      have hm : wordValue ((x :: xs).map decode32).reverse % B = x.val := by
        rw [wordValue_reverse_cons]
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [Nat.mod_eq_of_lt hsmall] at hm
      exact hm.symm

theorem low_candidate_refines (block : Bytes32) (ds : Digits) (q : U32)
    (h : AspisR1Post25Sampler.sampler.low_base_p_digits block = .ok (ds,q)) :
    values ds = ordinaryDigits (rank block) ∧ q.val = rank block / P^8 := by
  obtain ⟨outRank,ds1,q1,hlow,hhigh,hdigits,hremaining⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5.low_base_p_digits_success block
  have heq : (ds1,q1) = (ds,q) := Result.ok.inj (hlow.symm.trans h)
  have hed : ds1 = ds := congrArg Prod.fst heq
  have heq1 : q1 = q := congrArg Prod.snd heq
  subst ds1
  refine ⟨hdigits,?_⟩
  have hsmall : wordValue (words outRank).reverse < B := by
    rw [hremaining]
    have hqbound := rank_div_P8_le_256 (rank_lt block)
    have hB : 256 < B := by norm_num [B]
    omega
  rw [← heq1,hhigh,low_word_of_small_value outRank hsmall]
  exact hremaining
#print axioms low_candidate_refines
end AspisR1GammaCaller.DigitsModel
