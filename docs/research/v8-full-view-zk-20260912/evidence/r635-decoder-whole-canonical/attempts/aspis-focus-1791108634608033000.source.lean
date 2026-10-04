import AspisV8R19.R633PackedBlockResult
import AspisV8R19.R631DecoderChunkShape
import AspisV8R19.R632DecoderBlockArray
import AspisV8R19.R634DecoderPrefixCanonical
import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R635DecoderWholeCanonical
open Aeneas Aeneas.Std Result Aeneas.Std.WP
open R623PackedDecoderExecution R624DecoderInnerExecution R634DecoderPrefixCanonical

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
      | fail e =>
          simp only [hn, bind_tc_fail] at hexec
          cases hexec
      | div =>
          simp only [hn, bind_tc_div] at hexec
          cases hexec
      | ok next =>
          simp only [hn, bind_tc_ok] at hexec
          have hnext : next.val = count.val + 1 := by
            have hc : (count + 1#usize : Result Usize) ⦃ x => x.val = count.val + 1 ⦄ := by
              apply UScalar.add_spec
              have hbN : N.val ≤ Usize.max := by scalar_tac
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
          have hbound1 : 8 * (next.val + bs.length) ≤ N.val := by
            rw [hnext]
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hbound
          have hi := ih next (blockOutput8 count (blockValues ba) out)
            ((blockWords (blockValues ba)).foldl sourceInvalid invalid)
            hs hbound1 hexec
          exact (block_mask_backwards count ba out invalid hblock hi).1

theorem chunks_prefixCanonical {N : Usize} (bs : List (Slice U8))
    (count : Usize) (out : Array U32 N) (invalid : U32)
    (hchunks : ∀ b ∈ bs, b.val.length = 31)
    (hbound : 8 * (count.val + bs.length) ≤ N.val)
    (hprefix : prefixCanonical out (8 * count.val))
    (out1 : Array U32 N) (invalid1 : U32)
    (hexec : runChunks bs count out invalid = .ok (out1, invalid1))
    (haccepted : accepted invalid1) :
    prefixCanonical out1 (8 * (count.val + bs.length)) := by
  induction bs generalizing count out invalid with
  | nil =>
      simp only [runChunks, Result.ok.injEq, Prod.mk.injEq] at hexec
      obtain ⟨hout, _⟩ := hexec
      cases hout
      simpa using hprefix
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
      | fail e =>
          simp only [hn, bind_tc_fail] at hexec
          cases hexec
      | div =>
          simp only [hn, bind_tc_div] at hexec
          cases hexec
      | ok next =>
          simp only [hn, bind_tc_ok] at hexec
          have hnext : next.val = count.val + 1 := by
            have hc : (count + 1#usize : Result Usize) ⦃ x => x.val = count.val + 1 ⦄ := by
              apply UScalar.add_spec
              have hbN : N.val ≤ Usize.max := by scalar_tac
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
          have hbound1 : 8 * (next.val + bs.length) ≤ N.val := by
            rw [hnext]
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hbound
          have hi := chunks_mask_backwards bs next
            (blockOutput8 count (blockValues ba) out)
            ((blockWords (blockValues ba)).foldl sourceInvalid invalid)
            hs hbound1 out1 invalid1 hexec haccepted
          have hwords := (block_mask_backwards count ba out invalid hblock hi).2
          have hp := blockOutput8_prefixCanonical count (blockValues ba) out hblock hprefix hwords
          have hp1 : prefixCanonical (blockOutput8 count (blockValues ba) out) (8 * next.val) := by
            simpa only [hnext] using hp
          have final := ih next (blockOutput8 count (blockValues ba) out)
            ((blockWords (blockValues ba)).foldl sourceInvalid invalid)
            hs hbound1 hp1 hexec
          simpa only [hnext, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using final


/-- Any accepted actual decoder result exposes the complete source chunk
execution and an accepted final rejection accumulator. -/
theorem decoder_success_chunks {N : Usize} (bytes : Slice U8)
    (out out1 : Array U32 N)
    (hexec : AspisR614SelectedCombineBeta.query_arithmetic.r55_decode_into bytes out =
      .ok (core.result.Result.Ok (), out1)) :
    ∃ ce : core.slice.iter.ChunksExact U8, ∃ mask : U32,
      core.slice.Slice.chunks_exact bytes 31#usize = .ok ce ∧
      runChunks ce.chunks 0#usize out 0#u32 = .ok (out1, mask) ∧ accepted mask := by
  obtain ⟨ce, hce, _, _, _⟩ := R631DecoderChunkShape.source_chunks_shape bytes
  rw [decoder_outer_exact] at hexec
  unfold decode at hexec
  split at hexec
  · simp at hexec
  · cases hr : N % 8#usize with
    | fail e => simp [hr] at hexec
    | div => simp [hr] at hexec
    | ok rem =>
        simp only [hr, bind_tc_ok] at hexec
        split at hexec
        · simp at hexec
        · cases hd : N / 8#usize with
          | fail e => simp [hd] at hexec
          | div => simp [hd] at hexec
          | ok groups =>
              simp only [hd, bind_tc_ok, lift] at hexec
              split at hexec
              · simp at hexec
              · simp only [hce, bind_tc_ok] at hexec
                cases hrun : runChunks ce.chunks 0#usize out 0#u32 with
                | fail e => simp [hrun] at hexec
                | div => simp [hrun] at hexec
                | ok pair =>
                    obtain ⟨out2, mask⟩ := pair
                    simp only [hrun, bind_tc_ok, lift] at hexec
                    split at hexec
                    · simp at hexec
                    · rename_i hm
                      simp only [Result.ok.injEq, Prod.mk.injEq, true_and] at hexec
                      have hout : out2 = out1 := hexec
                      cases hout
                      refine ⟨ce, mask, hce, hrun, ?_⟩
                      unfold accepted R486ParserCanonicalMask.accepted
                      have hshift : Std.U32.wrapping_shr mask 31#u32 = 0#u32 := by
                        simpa only [bne_iff_ne, not_not] using hm
                      have hv := congrArg UScalar.bv hshift
                      change mask.bv >>> 31 = 0#32 at hv
                      exact hv

#print axioms decoder_success_chunks
#print axioms chunks_prefixCanonical
#print axioms block_mask_backwards
#print axioms chunks_mask_backwards
end AspisV8R19.R635DecoderWholeCanonical
