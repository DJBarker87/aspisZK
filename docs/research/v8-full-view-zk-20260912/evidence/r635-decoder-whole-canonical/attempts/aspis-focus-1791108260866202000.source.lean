import AspisV8R19.R633PackedBlockResult
import AspisV8R19.R631DecoderChunkShape
import AspisV8R19.R632DecoderBlockArray
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R635DecoderWholeCanonical
open Aeneas Aeneas.Std Result
open R623PackedDecoderExecution R624DecoderInnerExecution

abbrev accepted (mask : U32) := R486ParserCanonicalMask.accepted mask.bv

theorem block_mask_backwards {N : Usize} (block : Usize)
    (b : Array U8 31#usize) (out : Array U32 N) (invalid : U32)
    (hblock : 8 * (block.val + 1) ≤ N.val) :
    accepted ((blockWords (blockValues b)).foldl sourceInvalid invalid) →
      accepted invalid ∧
      ∀ value ∈ blockWords (blockValues b), value.val < 2147483647 :=
  (R633PackedBlockResult.block_mask_accepted block b out invalid hblock).mp

/-- Whole source chunk sequence, retaining arbitrary incoming invalid mask.
All chunk sizes and destination bounds are explicit and subsequently must be
derived from the selected caller. No source success premise is invented. -/
theorem chunks_mask_backwards {N : Usize} (bs : List (Slice U8))
    (count : Usize) (out : Array U32 N) (invalid : U32)
    (hchunks : ∀ b ∈ bs, b.val.length = 31)
    (hbound : 8 * (count.val + bs.length) ≤ N.val)
    (out1 : Array U32 N) (invalid1 : U32)
    (hexec : runChunks bs count out invalid = .ok (out1, invalid1))
    (haccepted : accepted invalid1) : accepted invalid := by
  induction bs generalizing count out invalid with
  | nil =>
      simp only [runChunks, Result.ok.injEq, Prod.mk.injEq] at hexec
      exact hexec.2 ▸ haccepted
  | cons b bs ih =>
      have hb : b.val.length = 31 := hchunks b (by simp)
      let ba : Array U8 31#usize := ⟨b.val, by simpa using hb⟩
      have hb_eq : Array.to_slice ba = b := by cases b; rfl
      have hblock : 8 * (count.val + 1) ≤ N.val := by
        simp only [List.length_cons] at hbound
        omega
      have hdecode := R633PackedBlockResult.block_result count ba out invalid hblock
      rw [hb_eq] at hdecode
      simp only [runChunks, hdecode] at hexec
      cases hn : count + 1#usize with
      | fail e => simp only [hn, bind_tc_fail] at hexec
      | div => simp only [hn, bind_tc_div] at hexec
      | ok next =>
          simp only [hn, bind_tc_ok] at hexec
          have hnext : next.val = count.val + 1 := by
            have := UScalar.add_spec hn
            omega
          have hs : ∀ c ∈ bs, c.val.length = 31 := by
            intro c hc
            exact hchunks c (by simp [hc])
          have hbound1 : 8 * (next.val + bs.length) ≤ N.val := by
            rw [hnext]
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hbound
          have hi := ih next (blockOutput8 count (blockValues ba) out)
            ((blockWords (blockValues ba)).foldl sourceInvalid invalid)
            hs hbound1 hexec haccepted
          exact (block_mask_backwards count ba out invalid hblock hi).1

#print axioms block_mask_backwards
#print axioms chunks_mask_backwards
end AspisV8R19.R635DecoderWholeCanonical
