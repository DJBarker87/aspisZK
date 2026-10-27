import R1Z.ProverRwDictionaryDerived
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryMerkle
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryDerived.selected ops with
    op119 := AspisR1ProverLeaf.state_only_private_merkle.private_leaf_hash}

def frame (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize
    [Array.to_slice (Array.make 2#usize [16#u8,tag]),value,Array.to_slice salt])

/-- The retained extracted leaf body invokes the same arbitrary callback
once with these three ordered slices. Failure and divergence remain visible. -/
theorem private_leaf (ops : ExternalFuns)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (tag : U8) (value : Slice U8) (salt : Array U8 32#usize) :
    (selected ops).op119 hash tag value salt = hash (frame tag value salt) := by
  change AspisR1ProverLeaf.state_only_private_merkle.private_leaf_hash hash tag value salt = _
  unfold AspisR1ProverLeaf.state_only_private_merkle.private_leaf_hash
    AspisR1ProverLeaf.state_only_private_merkle.private_leaf_hash_with_digest
    AspisR1ProverLeaf.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
    AspisR1ProverLeaf.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest
    AspisR1ProverLeaf.state_only_private_merkle.DOM_LEAF
  rfl

#print axioms private_leaf
end R1Z.ProverRwDictionaryMerkle
