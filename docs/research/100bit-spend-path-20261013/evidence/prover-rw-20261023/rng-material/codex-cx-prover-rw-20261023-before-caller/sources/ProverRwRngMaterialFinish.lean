import R1Z.ProverRwRngMaterialInvariant
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngMaterialFinish
open Aeneas Aeneas.Std Result ProverRwRngMaterialBody
open aspis_prover.state_only_entropy aspis_prover.state_only_hiding
open aspis_core.state_only_hiding ProverRwRngMaterialControl ProverRwRngMaterialPaths
open ProverRwRngMaterialInvariant
variable [TypeLeaves] [LocalLeaves]
abbrev Wrapped := zeroize.Zeroizing (Array U8 32#usize)
abbrev asrefEntropy (a : Secrets) :=
  zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref
    (Array.Insts.CoreConvertAsRefSlice U8 32#usize)
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a.field_mask_entropy
abbrev wrapSeed (seed : Array U8 32#usize) :=
  zeroize.Zeroizing.new
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed
abbrev clearEntropy (a : Secrets) :=
  zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize
    (Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a.field_mask_entropy

def sourceSeedInput (binding : Array U8 32#usize) (encoded : Array U8 81#usize)
    (entropySlice : Slice U8) : Slice (Slice U8) :=
  (Array.make 4#usize [POOL_V1_SOURCE_SEED_DOMAIN,binding.to_slice,encoded.to_slice,entropySlice]).to_slice

/-- The consumed flag is derived from the emitted producer, not assumed.
This consumer lemma takes its material reply only as an intermediate; the
concrete sampler theorem below discharges it using ordered component replies.
Explicit zeroize admission is a local leaf, not physical erasure. -/
theorem reserve_success_from_producer {S : Type} (store : Store S)
    (a : Secrets) (hash : Hash) (binding entropy sourceSeed : Array U8 32#usize)
    (c : Context) (s after : S) (encoded : Array U8 81#usize) (entropySlice : Slice U8)
    (m : StateOnlyMaskMaterial) (ack : PreReservedNonce) (wrapped cleared : Wrapped)
    (layout : LayoutOk a c)
    (reserved : store.reserve s c.statement_digest c.mask_nonce = .ok (true,after))
    (deref : derefEntropy a = .ok entropy)
    (built : material hash binding c entropy = .ok (.Ok m,ack))
    (encode : StateOnlyHidingContext.encode c = .ok encoded)
    (asref : asrefEntropy a = .ok entropySlice)
    (hashed : hash (sourceSeedInput binding encoded entropySlice) = .ok sourceSeed)
    (wrappedSeed : wrapSeed sourceSeed = .ok wrapped)
    (clear : clearEntropy a = .ok cleared) :
    reserveBuild store a hash binding c s =
      .ok (.Ok (⟨a.mask_nonce,binding,c,a.leaf_salt_seed,wrapped⟩,m),after) := by
  have consumed := (material_success_ack hash binding entropy c m ack built).1
  subst ack
  rcases layout with ⟨nonce,mask,factor⟩
  have compare : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      c.mask_nonce a.mask_nonce = .ok false := by rw [nonce,array_ne_self]
  simp only [derefEntropy] at deref
  simp only [material,freshAck] at built
  simp only [asrefEntropy] at asref
  simp only [sourceSeedInput] at hashed
  simp only [wrapSeed] at wrappedSeed
  simp only [clearEntropy] at clear
  unfold reserveBuild StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
  simp [compare,mask,factor,reserved,deref,built,usedAck,encode,asref,hashed,wrappedSeed,clear,lift,
    core.result.Result.Insts.CoreOpsTry.branch]

/-- Actual successful material derivation into returned post-reservation
secrets, from exact seed-hash and four ordered sampler component replies.
No whole-material equality or acknowledgment-consumed premise is retained. -/
theorem reserve_sample_success {S : Type} (store : Store S)
    (a : Secrets) (hash : Hash) (binding entropy seed sourceSeed : Array U8 32#usize)
    (c : Context) (s after : S) (encoded : Array U8 81#usize) (entropySlice : Slice U8)
    (cells : Cells) (active : Array Bool 1024#usize) (inactive : Usize)
    (s1 s2 s3 s4 : Expander) (c1 : alloc.vec.Vec aspis_core.field.M31)
    (columns : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (g h1 : alloc.vec.Vec aspis_core.field.QM31) (wrapped cleared : Wrapped)
    (layout : LayoutOk a c)
    (reserved : store.reserve s c.statement_digest c.mask_nonce = .ok (true,after))
    (deref : derefEntropy a = .ok entropy)
    (hcells : cellsReply = .ok (.Ok cells)) (hactive : activeReply = .ok (.Ok active))
    (nonzero : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 entropy
      (Array.repeat 32#usize 0#u8) = .ok false)
    (encode : StateOnlyHidingContext.encode c = .ok encoded)
    (seed_hash : hash (seedInput binding encoded entropy) = .ok seed)
    (hinactive : first_inactive_row active = .ok inactive)
    (hc1 : sample_mask_cells (initial hash seed) (Slice.len (alloc.vec.Vec.deref cells)) = .ok (.Ok c1,s1))
    (hcolumns : sample_mask_columns s1 inactive active = .ok (.Ok columns,s2))
    (hg : sample_mask_g s2 inactive active = .ok (.Ok g,s3))
    (hh1 : sample_mask_h1_padding s3 inactive active = .ok (.Ok h1,s4))
    (asref : asrefEntropy a = .ok entropySlice)
    (source_hash : hash (sourceSeedInput binding encoded entropySlice) = .ok sourceSeed)
    (wrappedSeed : wrapSeed sourceSeed = .ok wrapped)
    (clear : clearEntropy a = .ok cleared) :
    reserveBuild store a hash binding c s =
      .ok (.Ok (⟨a.mask_nonce,binding,c,a.leaf_salt_seed,wrapped⟩,
        ⟨c1,columns,g,h1,c.mask_nonce⟩),after) := by
  have built : material hash binding c entropy =
      .ok (.Ok ⟨c1,columns,g,h1,c.mask_nonce⟩,usedAck c) := by
    rw [material_reaches_layout hash binding entropy c cells active layout.2.1 layout.2.2 hcells hactive]
    exact layout_sample_success hash binding entropy seed c encoded _ active inactive s1 s2 s3 s4
      c1 columns g h1 nonzero encode seed_hash hinactive hc1 hcolumns hg hh1
  exact reserve_success_from_producer store a hash binding entropy sourceSeed c s after encoded entropySlice
    _ _ wrapped cleared layout reserved deref built encode asref source_hash wrappedSeed clear

#print axioms reserve_success_from_producer
#print axioms reserve_sample_success
end R1Z.ProverRwRngMaterialFinish
