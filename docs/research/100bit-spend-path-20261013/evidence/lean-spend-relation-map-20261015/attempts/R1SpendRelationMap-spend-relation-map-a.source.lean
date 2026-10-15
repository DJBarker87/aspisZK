import R1SpendDataMap
import R1NoteHashMap

/-! Ring-hom transport for the complete spend relation. This is a coordinate
embedding equivalence for already mapped witnesses; it does not claim that
arbitrary projections preserve witness validity. -/
set_option autoImplicit false
namespace AspisR1.SpendRelationMap

open R0P AspisPool.V7PairLeafOccupancy SpendRelation

variable {K L : Type} [Field K] [Field L]

private theorem map_eq_iff (f : K →+* L) (hf : Function.Injective f)
    (x y : K) : f x = f y ↔ x = y := by
  constructor
  · exact hf
  · intro h
    exact congrArg f h

private theorem map_zero_iff (f : K →+* L) (hf : Function.Injective f)
    (x : K) : f x = 0 ↔ x = 0 := by
  rw [← map_zero f]
  exact map_eq_iff f hf x 0

private theorem digest_injective (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (SpendDataMap.digest f : R0P.Digest K → R0P.Digest L) := by
  intro x y h
  funext i
  exact hf (congrFun h i)

private theorem pair_valid_map_iff (f : K →+* L) (hf : Function.Injective f)
    (p : PairLeaf K) : (SpendDataMap.pair f p).Valid ↔ p.Valid := by
  rcases p with ⟨firstCommitment, secondOccupied, secondCommitment,
    secondOccupancyInverse⟩
  simp [SpendDataMap.pair, SpendDataMap.digest, PairLeaf.Valid,
    PairLeaf.secondSentinel, map_zero_iff f hf, map_sub, map_mul, map_one]

private theorem pair_spendable_map_iff (f : K →+* L) (hf : Function.Injective f)
    (p : PairLeaf K) (b : Bool) :
    (SpendDataMap.pair f p).SelectedSlotIsSpendable b ↔
      p.SelectedSlotIsSpendable b := by
  cases b <;> simp [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied,
    SpendDataMap.pair, map_eq_iff f hf]

private theorem canonical_map_iff (f : K →+* L) (hf : Function.Injective f)
    (pub : Public K) :
    PublicOptionShape.canonical (SpendDataMap.mapPublic f pub) ↔
      PublicOptionShape.canonical pub := by
  cases hv : pub.variant with
  | privateTransfer =>
      cases hr : pub.recipient <;> cases ha : pub.withdrawalAmount <;>
        simp [PublicOptionShape.canonical, SpendDataMap.mapPublic, hv, hr, ha,
          map_eq_iff f hf]
  | withdrawal =>
      cases hr : pub.recipient <;> cases ha : pub.withdrawalAmount <;>
        simp [PublicOptionShape.canonical, SpendDataMap.mapPublic, hv, hr, ha,
          map_eq_iff f hf]

private theorem map_digest_noteCommitment (f : K →+* L)
    (pk : R0P.Digest K) (value asset : K) (salt : R0P.Digest K) :
    SpendDataMap.digest f (noteCommitment pk value asset salt) =
      noteCommitment (SpendDataMap.digest f pk) (f value)
        (f asset) (SpendDataMap.digest f salt) := by
  simpa [SpendDataMap.digest, PoseidonMap.mapDigest] using
    (NoteHashMap.map_noteCommitment f pk value asset salt)

private theorem map_digest_ownerKey (f : K →+* L) (sk : R0P.Digest K) :
    SpendDataMap.digest f (ownerKey sk) = ownerKey (SpendDataMap.digest f sk) := by
  simpa [SpendDataMap.digest, PoseidonMap.mapDigest] using
    (NoteHashMap.map_ownerKey f sk)

private theorem map_digest_nullifier (f : K →+* L)
    (sk salt : R0P.Digest K) :
    SpendDataMap.digest f (nullifierHash sk salt) =
      nullifierHash (SpendDataMap.digest f sk) (SpendDataMap.digest f salt) := by
  simpa [SpendDataMap.digest, PoseidonMap.mapDigest] using
    (NoteHashMap.map_nullifierHash f sk salt)

private theorem map_digest_merkleRoot (f : K →+* L) (leaf : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) :
    SpendDataMap.digest f (merkleRoot leaf path) =
      merkleRoot (SpendDataMap.digest f leaf) (SpendDataMap.path f path) := by
  simpa [SpendDataMap.digest, SpendDataMap.path, PoseidonMap.mapDigest,
    NoteHashMap.mapPath] using (NoteHashMap.map_merkleRoot f leaf path)

private theorem relation_map_iff (f : K →+* L) (hf : Function.Injective f)
    (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) :
    InputWitnessCore.Relation (SpendDataMap.mapPublic f pub) (f value)
      (SpendDataMap.digest f sk) (SpendDataMap.digest f salt)
      (SpendDataMap.path f path) (SpendDataMap.pair f pair) ↔
    InputWitnessCore.Relation pub value sk salt path pair := by
  let d := SpendDataMap.digest f
  constructor
  · intro h
    have hcommitMap : d (pair.selectedCommitment (path 0).1) =
        d (noteCommitment (ownerKey sk) value pub.assetId salt) := by
      calc
        d (pair.selectedCommitment (path 0).1) =
            (SpendDataMap.pair f pair).selectedCommitment (path 0).1 := by
              cases (path 0).1 <;> rfl
        _ = noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt) := h.commitment
        _ = d (noteCommitment (ownerKey sk) value pub.assetId salt) := by
              rw [map_digest_noteCommitment, map_digest_ownerKey]
    have hsiblingMap : d ((path 0).2) =
        d (if (path 0).1 then pair.firstCommitment else pair.secondCommitment) := by
      simpa [d, SpendDataMap.path, SpendDataMap.pair, SpendDataMap.digest] using h.sibling
    have hnullifierMap : d pub.nullifier = d (nullifierHash sk salt) := by
      calc
        d pub.nullifier = (SpendDataMap.mapPublic f pub).nullifier := rfl
        _ = nullifierHash (d sk) (d salt) := h.nullifier
        _ = d (nullifierHash sk salt) := (map_digest_nullifier f sk salt).symm
    have hmembershipMap : d pub.anchor = d (merkleRoot
        (noteCommitment (ownerKey sk) value pub.assetId salt) path) := by
      calc
        d pub.anchor = (SpendDataMap.mapPublic f pub).anchor := rfl
        _ = merkleRoot
              (noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt))
              (SpendDataMap.path f path) := h.membership
        _ = d (merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path) := by
              rw [map_digest_merkleRoot, map_digest_noteCommitment, map_digest_ownerKey]
    refine ⟨(pair_valid_map_iff f hf pair).mp h.valid,
      (pair_spendable_map_iff f hf pair (path 0).1).mp h.spendable,
      (digest_injective f hf hcommitMap), ?_,
      digest_injective f hf hnullifierMap,
      digest_injective f hf hmembershipMap⟩
    exact digest_injective f hf hsiblingMap
  · intro h
    have hcommitMap : d (pair.selectedCommitment (path 0).1) =
        d (noteCommitment (ownerKey sk) value pub.assetId salt) := congrArg d h.commitment
    have hsiblingMap : d ((path 0).2) =
        d (if (path 0).1 then pair.firstCommitment else pair.secondCommitment) :=
      congrArg d h.sibling
    have hnullifierMap : d pub.nullifier = d (nullifierHash sk salt) :=
      congrArg d h.nullifier
    have hmembershipMap : d pub.anchor = d (merkleRoot
        (noteCommitment (ownerKey sk) value pub.assetId salt) path) :=
      congrArg d h.membership
    refine ⟨(pair_valid_map_iff f hf pair).mpr h.valid,
      (pair_spendable_map_iff f hf pair (path 0).1).mpr h.spendable,
      ?_, ?_, ?_, ?_⟩
    · simpa [d, SpendDataMap.pair, SpendDataMap.digest, PairLeaf.selectedCommitment,
        map_digest_noteCommitment, map_digest_ownerKey] using hcommitMap
    · simpa [d, SpendDataMap.path, SpendDataMap.pair, SpendDataMap.digest] using hsiblingMap
    · simpa [d, SpendDataMap.mapPublic, SpendDataMap.digest,
        map_digest_nullifier] using hnullifierMap
    · simpa [d, SpendDataMap.mapPublic, SpendDataMap.path, SpendDataMap.digest,
        map_digest_merkleRoot, map_digest_noteCommitment, map_digest_ownerKey] using hmembershipMap

private theorem map_changeCommitment (f : K →+* L)
    (pub : Public K) (w : Witness K) :
    SpendDataMap.digest f (changeCommitment pub w) =
      changeCommitment (SpendDataMap.mapPublic f pub) (SpendDataMap.witness f w) := by
  simpa [changeCommitment, SpendDataMap.mapPublic, SpendDataMap.witness,
    SpendDataMap.digest, map_digest_noteCommitment] using
    (map_digest_noteCommitment f w.changeOwner (w.changeValue.val : K)
      pub.assetId w.changeSalt)

private theorem map_recipientCommitment (f : K →+* L)
    (pub : Public K) (w : Witness K) :
    SpendDataMap.digest f (recipientCommitment pub w) =
      recipientCommitment (SpendDataMap.mapPublic f pub) (SpendDataMap.witness f w) := by
  simpa [recipientCommitment, SpendDataMap.mapPublic, SpendDataMap.witness,
    SpendDataMap.digest, map_digest_noteCommitment] using
    (map_digest_noteCommitment f w.recipientOwner (w.outputValue.val : K)
      pub.assetId w.recipientSalt)

private theorem variantOutput_map_iff (f : K →+* L) (hf : Function.Injective f)
    (pub : Public K) (w : Witness K) :
    variantOutput (SpendDataMap.mapPublic f pub) (SpendDataMap.witness f w) ↔
      variantOutput pub w := by
  cases hv : pub.variant with
  | privateTransfer =>
      cases hr : pub.recipient <;>
        simp [variantOutput, SpendDataMap.mapPublic, hv, hr,
          map_recipientCommitment]
  | withdrawal =>
      cases ha : pub.withdrawalAmount <;>
        simp [variantOutput, SpendDataMap.mapPublic, SpendDataMap.witness, hv, ha,
          map_eq_iff f hf]

theorem rspend_map_iff (f : K →+* L) (pub : Public K) (w : Witness K) :
    Rspend (SpendDataMap.mapPublic f pub) (SpendDataMap.witness f w) ↔ Rspend pub w := by
  have hf : Function.Injective f := f.injective
  constructor
  · intro h
    rcases h with ⟨hcanonical, hrelation, hbalance, hchange, hvariant⟩
    have hvalue : f (w.inputValue.val : K) = (w.inputValue.val : L) := by simp
    refine ⟨(canonical_map_iff f hf pub).mp hcanonical, ?_,
      ?_, ?_, (variantOutput_map_iff f hf pub w).mp hvariant⟩
    · have hm := (relation_map_iff f hf pub (w.inputValue.val : K) w.sk w.salt
        w.path w.pair).mp (by simpa [SpendDataMap.witness, hvalue] using hrelation)
      simpa [SpendDataMap.witness] using hm
    · simpa [SpendDataMap.witness] using hbalance
    · apply digest_injective f hf
      calc
        SpendDataMap.digest f (pub.change) =
            changeCommitment (SpendDataMap.mapPublic f pub) (SpendDataMap.witness f w) := hchange
        _ = SpendDataMap.digest f (changeCommitment pub w) := (map_changeCommitment f pub w).symm
  · intro h
    rcases h with ⟨hcanonical, hrelation, hbalance, hchange, hvariant⟩
    have hvalue : f (w.inputValue.val : K) = (w.inputValue.val : L) := by simp
    refine ⟨(canonical_map_iff f hf pub).mpr hcanonical, ?_,
      ?_, ?_, (variantOutput_map_iff f hf pub w).mpr hvariant⟩
    · have hm := (relation_map_iff f hf pub (w.inputValue.val : K) w.sk w.salt
        w.path w.pair).mpr hrelation
      simpa [SpendDataMap.witness, hvalue] using hm
    · simpa [SpendDataMap.witness] using hbalance
    · calc
        (SpendDataMap.mapPublic f pub).change = SpendDataMap.digest f pub.change := rfl
        _ = SpendDataMap.digest f (changeCommitment pub w) := congrArg (SpendDataMap.digest f) hchange
        _ = changeCommitment (SpendDataMap.mapPublic f pub) (SpendDataMap.witness f w) := map_changeCommitment f pub w

#print axioms rspend_map_iff

end AspisR1.SpendRelationMap
