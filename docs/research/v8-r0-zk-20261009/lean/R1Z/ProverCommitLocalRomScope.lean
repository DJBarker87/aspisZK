import R1Z.ProverCommitOwnedReadBound
import R1Z.ProverCommitSourceCounts
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result
open R0Z.FsStatement
open R1Z.ProverCommitStepLoop (Hash)
open R1Z.ProverCommitSourceDecoder (L₂)

theorem short_backend_none {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (count : Nat)
    (too_many : 8*blocks < count) : samples (blockHash answers) domain count = none := by
  cases success : samples (blockHash answers) domain count with
  | none => rfl
  | some values =>
    have bound := samples_bound answers domain capacity count values success
    omega

/-- The nine-block ROM used by the local Kani scalar/tower harnesses cannot
supply even the second complete raw array. This is independent of every byte
answer and of the rejection pattern; increasing unwinding does not fix it. -/
theorem nine_block_source_none (answers : Fin 9 → OracleAnswer) :
    samples (blockHash answers)
      AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂ = none := by
  apply short_backend_none answers _ (by decide)
  have count := ProverCommitSourceDecoder.source_counts.2
  change L₂ = 4096 at count
  rw [count]
  decide

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- A whole-decoder proof cannot reuse a single local nine-block oracle reset.
This is not a counterexample to decoder, whose allocation is E₁/E₂ blocks. -/
theorem nine_block_decode_none (hash₁ : Hash) (answers : Fin 9 → OracleAnswer) :
    decodeWith (K := K) hash₁ (blockHash answers) = none := by
  simp only [decodeWith, rawArrays, nine_block_source_none]
  cases samples hash₁ AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN
      ProverCommitSourceDecoder.L₁ <;> rfl

#print axioms short_backend_none
#print axioms nine_block_source_none
#print axioms nine_block_decode_none
end R1Z.ProverCommitOwnedDecoder
