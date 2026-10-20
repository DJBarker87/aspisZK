import R1Z.ProverCommitSaltBytes
import R1Z.ProverCommitStreamBytes
import R1Z.ProverCommitLeafSource
import R1Z.PremisesR1PBin
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace R1Z.ProverCommitGrammarSource
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1
open R1Z.GamesR1PBin R1Z.LayoutR1PBin
open R1Z.ProverCommitSaltSource
variable {E₁ E₂ : ℕ}

/-! These are byte-carrier joins for the extracted callbacks. The image
hypotheses are explicit and no source R1ProverP instance is asserted. -/
theorem salt_gram (pub : List UInt8) (vtag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (sec : SecP) (d : OracleAnswer)
    (rest : RIdx → OracleAnswer) (tree : Fin 3) (u : Fib)
    (binding nonce secret : Bytes32) (tag : U8) (index : U32)
    (hb : binding.val.map ProverCommitSaltBytes.byte = ans (rest (qBind 1)))
    (hn : nonce.val.map ProverCommitSaltBytes.byte = ans (sec 0).1)
    (hs : secret.val.map ProverCommitSaltBytes.byte = ans (sec 2).1)
    (ht : ProverCommitSaltBytes.byte tag = treeTag tree)
    (hi : index.val = u.val) :
    ProverCommitSaltBytes.wireBytes (saltSlices binding nonce secret tag index) =
      gram pub vtag lv sec d rest
        (.inr (.inr (qSalt tree u)) : CPos E₁ E₂) := by
  rw [ProverCommitSaltBytes.salt_bytes, hb, hn, hs, ht, hi]
  rfl

theorem mask_gram (pub : List UInt8) (vtag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (sec : SecP) (d : OracleAnswer)
    (rest : RIdx → OracleAnswer) (c : Fin E₁)
    (seed : Bytes32) (counter : U64)
    (hs : seed.val.map ProverCommitStreamBytes.byte = ans (rest (qSeed 0)))
    (hc : counter.val = c.val) :
    ProverCommitStreamBytes.wireBytes
        (ProverCommitStreamSource.blockSlices
          AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN seed counter) =
      gram pub vtag lv sec d rest (.inr (.inl (.inl c)) : CPos E₁ E₂) := by
  rw [ProverCommitStreamBytes.block_bytes, ProverCommitStreamBytes.mask_domain, hs, hc]
  rfl

theorem source_gram (pub : List UInt8) (vtag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (sec : SecP) (d : OracleAnswer)
    (rest : RIdx → OracleAnswer) (c : Fin E₂)
    (seed : Bytes32) (counter : U64)
    (hs : seed.val.map ProverCommitStreamBytes.byte = ans (rest (qSeed 2)))
    (hc : counter.val = c.val) :
    ProverCommitStreamBytes.wireBytes
        (ProverCommitStreamSource.blockSlices
          AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN seed counter) =
      gram pub vtag lv sec d rest (.inr (.inl (.inr c)) : CPos E₁ E₂) := by
  rw [ProverCommitStreamBytes.block_bytes, ProverCommitStreamBytes.source_domain, hs, hc]
  rfl

theorem leaf_gram (pub : List UInt8) (vtag : UInt8)
    (lv : Fin 3 → Fib → List UInt8) (sec : SecP) (d : OracleAnswer)
    (rest : RIdx → OracleAnswer) (tree : Fin 3) (u : Fib)
    (value : Slice U8) (salt : Bytes32)
    (hv : value.val.map ProverCommitLeafSource.byte = lv tree u)
    (hs : salt.val.map ProverCommitLeafSource.byte = ans (rest (qSalt tree u))) :
    ProverCommitLeafSource.wireBytes
        (ProverCommitLeafSource.leafSlices (ProverCommitLeafSource.tagOf tree) value salt) =
      gram pub vtag lv sec d rest (.inr (.inr (qLeaf tree u)) : CPos E₁ E₂) := by
  rw [ProverCommitLeafSource.leaf_shared, hv, hs]
  simp only [AspisR1.SharedBinaryRecordGrammar.leafInput]
  rfl

#print axioms salt_gram
#print axioms mask_gram
#print axioms source_gram
#print axioms leaf_gram
end R1Z.ProverCommitGrammarSource
