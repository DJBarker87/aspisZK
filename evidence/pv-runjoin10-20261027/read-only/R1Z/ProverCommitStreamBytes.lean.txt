import R1Z.ProverCommitStreamSource
import R1Z.ProverCommitSaltBytes
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.ProverCommitStreamBytes
open R1Z.ProverCommitStreamSource AspisR1ProverStreams
abbrev byte := R1Z.ProverCommitSaltBytes.byte

def wireBytes (s : Slice (Slice U8)) : List UInt8 :=
  (s.val.flatMap (fun x => x.val)).map byte

theorem block_bytes (domain : Slice U8) (seed : Bytes32) (counter : U64) :
    wireBytes (blockSlices domain seed counter) =
      domain.val.map byte ++ seed.val.map byte ++ LayoutR1PBin.le64 counter.val := by
  simp [wireBytes, blockSlices, Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make,
    List.map_append, List.append_assoc, R1Z.ProverCommitSaltBytes.le64_source]

theorem mask_domain :
    state_only_hiding.MASK_EXPAND_DOMAIN.val.map byte = LayoutR1PBin.dExp1 := by
  unfold state_only_hiding.MASK_EXPAND_DOMAIN
  rfl

theorem source_domain :
    state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN.val.map byte = LayoutR1PBin.dExp2 := by
  unfold state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN
  rfl

theorem mask_seed_domain :
    state_only_hiding.MASK_SEED_DOMAIN.val.map byte = LayoutR1PBin.dMaskSeed := by
  unfold state_only_hiding.MASK_SEED_DOMAIN
  rfl

/-- This is the bounded machine step used at refill, not a claim that an
unrestricted wrapping counter never repeats. Source read-count transport
must supply the bound for every actual refill. -/
theorem counter_step (counter : U64) (bound : counter.val + 1 < 2^64) :
    (core.num.U64.wrapping_add counter 1#u64).val = counter.val + 1 := by
  rw [core.num.U64.wrapping_add_val_eq]
  have one : (1#u64).val = 1 := by scalar_tac
  simp only [one, UScalar.size, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt bound

/-- The source's four-byte slices partition a 32-byte block into eight words.
No enumeration of a large finite carrier is involved. -/
def wordByteEquiv : (Fin 8 × Fin 4) ≃ Fin 32 := finProdFinEquiv

theorem word_byte_index (word : Fin 8) (limb : Fin 4) :
    (wordByteEquiv (word,limb)).val = 4*word.val + limb.val := by
  change limb.val + 4*word.val = 4*word.val + limb.val
  omega

#print axioms block_bytes
#print axioms mask_domain
#print axioms source_domain
#print axioms mask_seed_domain
#print axioms counter_step
#print axioms word_byte_index
end R1Z.ProverCommitStreamBytes
