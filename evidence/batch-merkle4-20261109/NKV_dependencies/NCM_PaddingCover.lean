import NCM_PaddingScan
import Port4B_Padding

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_PaddingCover
open Aeneas Aeneas.Std Result

/-- Every complete chunk is a subrange of the original suffix. -/
theorem member (xs : List U8) (chunk : List U8)
    (inChunks : chunk ∈ (List.toChunksExact 8 (by decide) xs).1) (b : U8) (inChunk : b ∈ chunk) : b ∈ xs := by
  by_cases short : xs.length < 8
  · rw [List.toChunksExact] at inChunks
    simp only [dif_pos short,List.not_mem_nil] at inChunks
  · rw [List.toChunksExact] at inChunks
    simp only [dif_neg short,List.mem_cons] at inChunks
    rcases inChunks with rfl|later
    · exact List.mem_of_mem_take inChunk
    · exact List.mem_of_mem_drop (member (xs.drop 8) chunk later b inChunk)
termination_by xs.length
decreasing_by simp only [List.length_drop];omega

/-- Whole-word coverage in both directions. The forward direction imports
the existing coverage result; the reverse uses only original-byte membership. -/
theorem raw_zero (xs : List U8) (whole : xs.length%8 = 0) :
    (∀ c ∈ (List.toChunksExact 8 (by decide) xs).1, ∀ b ∈ c, b = 0#u8) ↔
      ∀ b ∈ xs, b = 0#u8 := by
  constructor
  · exact Port4B_Padding.chunks_zero xs whole
  · intro zero c inChunks b inChunk
    exact zero b (member xs c inChunks b inChunk)

/-- The actual chunks_exact constructor supplies the SAME partition. A final
partial word is excluded by the proved physical suffix-width condition. -/
theorem zero (padding : Slice U8) (ce : NCE_PaddingCuts.Iter)
    (constructed : core.slice.Slice.chunks_exact padding 8#usize = ok ce)
    (whole : padding.val.length%8 = 0) :
    (∀ c ∈ ce.chunks, ∀ b ∈ c.val, b = 0#u8) ↔ ∀ b ∈ padding.val, b = 0#u8 := by
  unfold core.slice.Slice.chunks_exact at constructed
  split at constructed
  next positive =>
    have same := Result.ok.inj constructed
    subst ce
    constructor
    · intro all
      apply (raw_zero padding.val whole).mp
      intro c mem
      exact all _ (List.mem_map.mpr ⟨⟨c,mem⟩,by simp,rfl⟩)
    · intro all c mem
      obtain ⟨raw,member,rfl⟩ := List.mem_map.mp mem
      rcases raw with ⟨bytes,rawMember⟩
      intro b inChunk
      exact all b (NCM_PaddingCover.member padding.val bytes rawMember b inChunk)
  next impossible => simp at impossible

#print axioms member
#print axioms raw_zero
#print axioms zero
end AspisR1.NCM_PaddingCover
end
