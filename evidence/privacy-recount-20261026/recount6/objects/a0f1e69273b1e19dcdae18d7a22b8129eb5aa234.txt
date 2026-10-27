import AspisR1ProverStreams.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.ProverCommitStreamSource
open AspisR1ProverStreams
abbrev Bytes32 := Aeneas.Std.Array U8 32#usize
abbrev Hash := Slice (Slice U8) → Result Bytes32

def blockSlices (domain : Slice U8) (seed : Bytes32) (counter : U64) : Slice (Slice U8) :=
  Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 3#usize [domain,
    Aeneas.Std.Array.to_slice seed,
    Aeneas.Std.Array.to_slice (core.num.U64.to_le_bytes counter)])

theorem mask_block (hash : Hash) (seed : Bytes32) (counter : U64) :
    state_only_hiding.state_only_mask_expander_block hash seed counter =
      hash (blockSlices state_only_hiding.MASK_EXPAND_DOMAIN seed counter) := by
  simp [state_only_hiding.state_only_mask_expander_block, blockSlices, lift]

theorem source_block (hash : Hash) (seed : Bytes32) (counter : U64) :
    state_only_entropy.profile21_source_expander_block hash seed counter =
      hash (blockSlices state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN seed counter) := by
  simp [state_only_entropy.profile21_source_expander_block, blockSlices, lift]

def seedSlices (binding : Bytes32) (context : Aeneas.Std.Array U8 81#usize)
    (entropy : Bytes32) : Slice (Slice U8) :=
  Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 4#usize [state_only_hiding.MASK_SEED_DOMAIN,
    Aeneas.Std.Array.to_slice binding, Aeneas.Std.Array.to_slice context,
    Aeneas.Std.Array.to_slice entropy])

theorem mask_seed (hash : Hash) (binding entropy : Bytes32)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (encoded : Aeneas.Std.Array U8 81#usize)
    (nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      entropy (Aeneas.Std.Array.repeat 32#usize 0#u8) = ok false)
    (encode : aspis_core.state_only_hiding.StateOnlyHidingContext.encode context = ok encoded) :
    state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy =
      (do let answer ← hash (seedSlices binding encoded entropy)
          ok (.Ok answer)) := by
  simp [state_only_hiding.derive_state_only_mask_seed_from_entropy_ref,
    nonzero, encode, seedSlices, lift]

#print axioms mask_block
#print axioms source_block
#print axioms mask_seed
end R1Z.ProverCommitStreamSource
