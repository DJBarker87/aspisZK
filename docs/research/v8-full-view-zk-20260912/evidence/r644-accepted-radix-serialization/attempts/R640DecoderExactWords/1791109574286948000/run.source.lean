import AspisV8R19.R635DecoderWholeCanonical
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R640DecoderExactWords
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open R623PackedDecoderExecution R624DecoderInnerExecution

def wordsOfChunks : (bs : List (Slice U8)) →
    (∀ b ∈ bs, b.val.length = 31) → List U32
  | [], _ => []
  | b :: bs, h =>
      let ba : Array U8 31#usize := ⟨b.val, by simpa using h b (by simp)⟩
      blockWords (blockValues ba) ++
        wordsOfChunks bs (by intro c hc; exact h c (by simp [hc]))

/-- The exact list of source-extracted masked words fills the remaining output
array. The full destination bound is explicit; the selected header supplies
it in the dependent accepted-decoder bridge. -/
theorem chunks_filled_output {N : Usize} (bs : List (Slice U8))
    (count : Usize) (out : Array U32 N) (invalid : U32)
    (hchunks : ∀ b ∈ bs, b.val.length = 31)
    (hfull : 8 * (count.val + bs.length) = N.val)
    (out1 : Array U32 N) (mask : U32)
    (hexec : runChunks bs count out invalid = .ok (out1, mask)) :
    out1.val = out.val.take (8 * count.val) ++ wordsOfChunks bs hchunks := by
  induction bs generalizing count out invalid with
  | nil =>
      simp only [runChunks, Result.ok.injEq, Prod.mk.injEq] at hexec
      obtain ⟨hout, _⟩ := hexec
      cases hout
      simp only [List.length_nil, Nat.add_zero] at hfull
      simp only [wordsOfChunks, List.append_nil, hfull]
      exact (List.take_of_length_le (by rw [out1.property])).symm
  | cons b bs ih =>
      have hb : b.val.length = 31 := hchunks b (by simp)
      let ba : Array U8 31#usize := ⟨b.val, by simpa using hb⟩
      have hb_eq : Array.to_slice ba = b := by cases b; rfl
      have hblock : 8 * (count.val + 1) ≤ N.val := by
        simp only [List.length_cons] at hfull
        omega
      have hdecode := R633PackedBlockResult.block_result count ba out invalid hblock
      rw [hb_eq] at hdecode
      simp only [runChunks, hdecode] at hexec
      cases hn : count + 1#usize with
      | fail e => simp only [hn, bind_tc_fail] at hexec; cases hexec
      | div => simp only [hn, bind_tc_div] at hexec; cases hexec
      | ok next =>
          simp only [hn, bind_tc_ok] at hexec
          have hnext : next.val = count.val + 1 := by
            have hc : (count + 1#usize : Result Usize) ⦃ x => x.val = count.val + 1 ⦄ := by
              apply UScalar.add_spec
              have hN : N.val ≤ Usize.max := by scalar_tac
              simp only [UScalar.max_USize_eq]
              change count.val + 1 ≤ Usize.max
              omega
            obtain ⟨x, hx, hxval⟩ := spec_imp_exists hc
            rw [hn] at hx
            cases hx
            exact hxval
          have hs : ∀ c ∈ bs, c.val.length = 31 := by
            intro c hc
            exact hchunks c (by simp [hc])
          have hfull1 : 8 * (next.val + bs.length) = N.val := by
            rw [hnext]
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hfull
          have hi := ih next (blockOutput8 count (blockValues ba) out)
            ((blockWords (blockValues ba)).foldl sourceInvalid invalid) hs hfull1 hexec
          rw [hi]
          have hsegment := R632DecoderBlockArray.blockOutput8_segment count (blockValues ba) out hblock
          rw [hsegment, hnext]
          have hprefixlen :
              (out.val.take (8 * count.val) ++ blockWords (blockValues ba)).length =
                8 * (count.val + 1) := by
            have hout := out.property
            have hlen : (blockWords (blockValues ba)).length = 8 := by simp [blockWords]
            simp only [List.length_append, List.length_take, hlen]
            rw [Nat.min_eq_left (by omega)]
            omega
          rw [List.take_append_of_le_length (by rw [hprefixlen])]
          rw [List.take_of_length_le (by rw [hprefixlen])]
          simp only [wordsOfChunks, List.append_assoc]
          rfl

#print axioms wordsOfChunks
#print axioms chunks_filled_output
end AspisV8R19.R640DecoderExactWords
