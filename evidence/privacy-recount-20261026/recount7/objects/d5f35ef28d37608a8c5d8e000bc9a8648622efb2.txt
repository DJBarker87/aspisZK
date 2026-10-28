import R1Z.PV_RunJoin_SpendDataMap
import R1Z.PV_RunJoin_NoteHashMap
import R1Z.PV_RunJoin_AppendBindingMap

/-! Ring-hom transport for the complete spend relation. This is a coordinate
embedding equivalence for already mapped witnesses; it does not claim that
arbitrary projections preserve witness validity. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SpendRelationMap
open AspisR1

open R0P AspisPool.V7PairLeafOccupancy SpendRelation

variable {K L : Type} [Field K] [Field L]

theorem map_eq_iff (f : K →+* L) (hf : Function.Injective f)
    (x y : K) : f x = f y ↔ x = y := by
  constructor
  · intro h
    exact hf h
  · intro h
    exact congrArg f h

theorem map_zero_iff (f : K →+* L) (hf : Function.Injective f)
    (x : K) : f x = 0 ↔ x = 0 := by
  rw [← map_zero f]
  exact map_eq_iff f hf x 0

theorem digest_injective (f : K →+* L) (hf : Function.Injective f) :
    Function.Injective (PV_RunJoin_SpendDataMap.digest f : R0P.Digest K → R0P.Digest L) := by
  intro x y h
  funext i
  exact hf (congrFun h i)

theorem pair_valid_map_iff (f : K →+* L) (hf : Function.Injective f)
    (p : PairLeaf K) : (PV_RunJoin_SpendDataMap.pair f p).Valid ↔ p.Valid := by
  rcases p with ⟨firstCommitment, secondOccupied, secondCommitment,
    secondOccupancyInverse⟩
  change
    (f secondOccupied * (f secondOccupied - 1) = 0 ∧
      f (secondCommitment ⟨7, by decide⟩) * f secondOccupancyInverse =
        f secondOccupied ∧
      (1 - f secondOccupied) * f secondOccupancyInverse = 0 ∧
      ∀ lane, (1 - f secondOccupied) * f (secondCommitment lane) = 0) ↔
    (secondOccupied * (secondOccupied - 1) = 0 ∧
      secondCommitment ⟨7, by decide⟩ * secondOccupancyInverse = secondOccupied ∧
      (1 - secondOccupied) * secondOccupancyInverse = 0 ∧
      ∀ lane, (1 - secondOccupied) * secondCommitment lane = 0)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h1' : f (secondOccupied * (secondOccupied - 1)) = f 0 := by
      simpa [map_sub, map_mul] using h1
    have h2' : f (secondCommitment ⟨7, by decide⟩ * secondOccupancyInverse) =
        f secondOccupied := by simpa [map_mul] using h2
    have h3' : f ((1 - secondOccupied) * secondOccupancyInverse) = f 0 := by
      simpa [map_sub, map_mul] using h3
    refine ⟨(map_eq_iff f hf _ _).mp h1', (map_eq_iff f hf _ _).mp h2',
      (map_eq_iff f hf _ _).mp h3', ?_⟩
    intro lane
    have h4' : f ((1 - secondOccupied) * secondCommitment lane) = f 0 := by
      simpa [map_sub, map_mul] using h4 lane
    exact (map_eq_iff f hf _ _).mp h4'
  · rintro ⟨h1, h2, h3, h4⟩
    have h1' : f (secondOccupied * (secondOccupied - 1)) = f 0 := congrArg f h1
    have h2' : f (secondCommitment ⟨7, by decide⟩ * secondOccupancyInverse) =
        f secondOccupied := congrArg f h2
    have h3' : f ((1 - secondOccupied) * secondOccupancyInverse) = f 0 := congrArg f h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [map_sub, map_mul] using h1'
    · simpa [map_mul] using h2'
    · simpa [map_sub, map_mul] using h3'
    · intro lane
      have h4' : f ((1 - secondOccupied) * secondCommitment lane) = f 0 :=
        congrArg f (h4 lane)
      simpa [map_sub, map_mul] using h4'

theorem pair_spendable_map_iff (f : K →+* L) (hf : Function.Injective f)
    (p : PairLeaf K) (b : Bool) :
    (PV_RunJoin_SpendDataMap.pair f p).SelectedSlotIsSpendable b ↔
      p.SelectedSlotIsSpendable b := by
  cases b with
  | false => simp [PairLeaf.SelectedSlotIsSpendable, PairLeaf.selectedOccupied,
      PV_RunJoin_SpendDataMap.pair]
  | true =>
      change f p.secondOccupied = 1 ↔ p.secondOccupied = 1
      rw [← map_one f]
      exact map_eq_iff f hf _ _

theorem canonical_map_iff (f : K →+* L) (hf : Function.Injective f)
    (pub : Public K) :
    PublicOptionShape.canonical (PV_RunJoin_SpendDataMap.mapPublic f pub) ↔
      PublicOptionShape.canonical pub := by
  cases hv : pub.variant with
  | privateTransfer =>
      cases hr : pub.recipient <;> cases ha : pub.withdrawalAmount <;>
        simp [PublicOptionShape.canonical, PV_RunJoin_SpendDataMap.mapPublic, hv, hr, ha,
          map_zero_iff f hf]
  | withdrawal =>
      cases hr : pub.recipient <;> cases ha : pub.withdrawalAmount <;>
        simp [PublicOptionShape.canonical, PV_RunJoin_SpendDataMap.mapPublic, hv, hr, ha,
          map_zero_iff f hf]

theorem map_digest_noteCommitment (f : K →+* L)
    (pk : R0P.Digest K) (value asset : K) (salt : R0P.Digest K) :
    PV_RunJoin_SpendDataMap.digest f (noteCommitment pk value asset salt) =
      noteCommitment (PV_RunJoin_SpendDataMap.digest f pk) (f value)
        (f asset) (PV_RunJoin_SpendDataMap.digest f salt) := by
  change PV_RunJoin_PoseidonMap.mapDigest f (noteCommitment pk value asset salt) = _
  exact PV_RunJoin_NoteHashMap.map_noteCommitment f pk value asset salt

theorem map_digest_ownerKey (f : K →+* L) (sk : R0P.Digest K) :
    PV_RunJoin_SpendDataMap.digest f (ownerKey sk) = ownerKey (PV_RunJoin_SpendDataMap.digest f sk) := by
  change PV_RunJoin_PoseidonMap.mapDigest f (ownerKey sk) = _
  exact PV_RunJoin_NoteHashMap.map_ownerKey f sk

theorem map_digest_nullifier (f : K →+* L)
    (sk salt : R0P.Digest K) :
    PV_RunJoin_SpendDataMap.digest f (nullifierHash sk salt) =
      nullifierHash (PV_RunJoin_SpendDataMap.digest f sk) (PV_RunJoin_SpendDataMap.digest f salt) := by
  change PV_RunJoin_PoseidonMap.mapDigest f (nullifierHash sk salt) = _
  exact PV_RunJoin_NoteHashMap.map_nullifierHash f sk salt

theorem map_digest_merkleRoot (f : K →+* L) (leaf : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) :
    PV_RunJoin_SpendDataMap.digest f (merkleRoot leaf path) =
      merkleRoot (PV_RunJoin_SpendDataMap.digest f leaf) (PV_RunJoin_SpendDataMap.path f path) := by
  change PV_RunJoin_PoseidonMap.mapDigest f (merkleRoot leaf path) =
    merkleRoot (PV_RunJoin_PoseidonMap.mapDigest f leaf) (PV_RunJoin_NoteHashMap.mapPath f path)
  exact PV_RunJoin_NoteHashMap.map_merkleRoot f leaf path

theorem relation_map_iff (f : K →+* L) (hf : Function.Injective f)
    (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) :
    InputWitnessCore.Relation (PV_RunJoin_SpendDataMap.mapPublic f pub) (f value)
      (PV_RunJoin_SpendDataMap.digest f sk) (PV_RunJoin_SpendDataMap.digest f salt)
      (PV_RunJoin_SpendDataMap.path f path) (PV_RunJoin_SpendDataMap.pair f pair) ↔
    InputWitnessCore.Relation pub value sk salt path pair := by
  let d := PV_RunJoin_SpendDataMap.digest f
  have howner : d (ownerKey sk) = ownerKey (d sk) := by
    simpa [d] using map_digest_ownerKey f sk
  have hnote : d (noteCommitment (ownerKey sk) value pub.assetId salt) =
      noteCommitment (d (ownerKey sk)) (f value) (f pub.assetId) (d salt) := by
    simpa [d] using map_digest_noteCommitment f (ownerKey sk) value pub.assetId salt
  have hroot : ∀ leaf, d (merkleRoot leaf path) =
      merkleRoot (d leaf) (PV_RunJoin_SpendDataMap.path f path) := by
    intro leaf
    simpa [d] using map_digest_merkleRoot f leaf path
  constructor
  · intro h
    have hcommitMap : d (pair.selectedCommitment (path 0).1) =
        d (noteCommitment (ownerKey sk) value pub.assetId salt) := by
      calc
        d (pair.selectedCommitment (path 0).1) =
            (PV_RunJoin_SpendDataMap.pair f pair).selectedCommitment (path 0).1 := by
              cases (path 0).1 <;> rfl
        _ = noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt) := h.commitment
        _ = d (noteCommitment (ownerKey sk) value pub.assetId salt) := by
              rw [← howner]
              exact hnote.symm
    have hsiblingMap : d ((path 0).2) =
        d (if (path 0).1 then pair.firstCommitment else pair.secondCommitment) := by
      cases hb : (path 0).1 <;>
        simpa [d, PV_RunJoin_SpendDataMap.path, PV_RunJoin_SpendDataMap.pair, hb] using h.sibling
    have hnullifierMap : d pub.nullifier = d (nullifierHash sk salt) := by
      calc
        d pub.nullifier = (PV_RunJoin_SpendDataMap.mapPublic f pub).nullifier := rfl
        _ = nullifierHash (d sk) (d salt) := h.nullifier
        _ = d (nullifierHash sk salt) := (map_digest_nullifier f sk salt).symm
    have hmembershipMap : d pub.anchor = d (merkleRoot
        (noteCommitment (ownerKey sk) value pub.assetId salt) path) := by
      calc
        d pub.anchor = (PV_RunJoin_SpendDataMap.mapPublic f pub).anchor := rfl
        _ = merkleRoot
              (noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt))
              (PV_RunJoin_SpendDataMap.path f path) := h.membership
        _ = merkleRoot (d (noteCommitment (ownerKey sk) value pub.assetId salt))
              (PV_RunJoin_SpendDataMap.path f path) := by rw [← howner, hnote.symm]
        _ = d (merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path) :=
              (hroot _).symm
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
    have hmappedNote : noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt) =
        d (noteCommitment (ownerKey sk) value pub.assetId salt) := by
      rw [← howner]
      exact hnote.symm
    refine ⟨(pair_valid_map_iff f hf pair).mpr h.valid,
      (pair_spendable_map_iff f hf pair (path 0).1).mpr h.spendable,
      ?_, ?_, ?_, ?_⟩
    · calc
          (PV_RunJoin_SpendDataMap.pair f pair).selectedCommitment (path 0).1 =
              d (pair.selectedCommitment (path 0).1) := by cases (path 0).1 <;> rfl
          _ = d (noteCommitment (ownerKey sk) value pub.assetId salt) := hcommitMap
          _ = noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt) :=
              hmappedNote.symm
    · calc
        (PV_RunJoin_SpendDataMap.path f path 0).2 = d ((path 0).2) := rfl
        _ = d (if (path 0).1 then pair.firstCommitment else pair.secondCommitment) := hsiblingMap
        _ = if (path 0).1 then (PV_RunJoin_SpendDataMap.pair f pair).firstCommitment
              else (PV_RunJoin_SpendDataMap.pair f pair).secondCommitment := by cases (path 0).1 <;> rfl
    · calc
        (PV_RunJoin_SpendDataMap.mapPublic f pub).nullifier = d pub.nullifier := rfl
        _ = d (nullifierHash sk salt) := hnullifierMap
        _ = nullifierHash (d sk) (d salt) := map_digest_nullifier f sk salt
    · calc
        (PV_RunJoin_SpendDataMap.mapPublic f pub).anchor = d pub.anchor := rfl
        _ = d (merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path) := hmembershipMap
        _ = merkleRoot (d (noteCommitment (ownerKey sk) value pub.assetId salt))
              (PV_RunJoin_SpendDataMap.path f path) := hroot _
        _ = merkleRoot (noteCommitment (ownerKey (d sk)) (f value) (f pub.assetId) (d salt))
              (PV_RunJoin_SpendDataMap.path f path) := by rw [hmappedNote.symm]

theorem map_changeCommitment (f : K →+* L)
    (pub : Public K) (w : Witness K) :
    PV_RunJoin_SpendDataMap.digest f (changeCommitment pub w) =
      changeCommitment (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) := by
  simpa [changeCommitment, PV_RunJoin_SpendDataMap.mapPublic, PV_RunJoin_SpendDataMap.witness,
    PV_RunJoin_SpendDataMap.digest, map_digest_noteCommitment] using
    (map_digest_noteCommitment f w.changeOwner (w.changeValue.val : K)
      pub.assetId w.changeSalt)

theorem map_recipientCommitment (f : K →+* L)
    (pub : Public K) (w : Witness K) :
    PV_RunJoin_SpendDataMap.digest f (recipientCommitment pub w) =
      recipientCommitment (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) := by
  simpa [recipientCommitment, PV_RunJoin_SpendDataMap.mapPublic, PV_RunJoin_SpendDataMap.witness,
    PV_RunJoin_SpendDataMap.digest, map_digest_noteCommitment] using
    (map_digest_noteCommitment f w.recipientOwner (w.outputValue.val : K)
      pub.assetId w.recipientSalt)

theorem variantOutput_map_iff (f : K →+* L) (hf : Function.Injective f)
    (pub : Public K) (w : Witness K) :
    variantOutput (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) ↔
      variantOutput pub w := by
  have hd : Function.Injective (PV_RunJoin_SpendDataMap.digest f : R0P.Digest K → R0P.Digest L) :=
    digest_injective f hf
  have hcast : f (w.outputValue.val : K) = (w.outputValue.val : L) := by simp
  cases hv : pub.variant with
  | privateTransfer =>
      cases hr : pub.recipient with
      | none => simp [variantOutput, PV_RunJoin_SpendDataMap.mapPublic, hv, hr]
      | some r =>
          simp only [variantOutput, hv, hr, PV_RunJoin_SpendDataMap.mapPublic, PV_RunJoin_SpendDataMap.witness,
            Option.map_some, Option.some.injEq]
          change PV_RunJoin_SpendDataMap.digest f r =
              recipientCommitment (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) ↔
            r = recipientCommitment pub w
          constructor
          · intro h
            apply hd
            calc
              PV_RunJoin_SpendDataMap.digest f r =
                  recipientCommitment (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) := h
              _ = PV_RunJoin_SpendDataMap.digest f (recipientCommitment pub w) :=
                  (map_recipientCommitment f pub w).symm
          · intro h
            rw [h, map_recipientCommitment]
  | withdrawal =>
      cases ha : pub.withdrawalAmount with
      | none => simp [variantOutput, PV_RunJoin_SpendDataMap.mapPublic, hv, ha]
      | some amount =>
          simp only [variantOutput, hv, ha, PV_RunJoin_SpendDataMap.mapPublic, PV_RunJoin_SpendDataMap.witness,
            Option.map_some, Option.some.injEq]
          change f amount = (w.outputValue.val : L) ↔ amount = (w.outputValue.val : K)
          rw [← hcast]
          exact map_eq_iff f hf _ _

theorem rspend_map_iff (f : K →+* L) (pub : Public K) (w : Witness K) :
    Rspend (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) ↔ Rspend pub w := by
  have hf : Function.Injective f := f.injective
  constructor
  · intro h
    rcases h with ⟨hcanonical, hrelation, hbalance, hchange, hvariant, happend⟩
    have hvalue : f (w.inputValue.val : K) = (w.inputValue.val : L) := by simp
    refine ⟨(canonical_map_iff f hf pub).mp hcanonical, ?_,
      ?_, ?_, (variantOutput_map_iff f hf pub w).mp hvariant,
      (PV_RunJoin_AppendBindingMap.appendBinding_map_iff f pub).mp happend⟩
    · have hm := (relation_map_iff f hf pub (w.inputValue.val : K) w.sk w.salt
        w.path w.pair).mp (by simpa [PV_RunJoin_SpendDataMap.witness, hvalue] using hrelation)
      simpa [PV_RunJoin_SpendDataMap.witness] using hm
    · simpa [PV_RunJoin_SpendDataMap.witness] using hbalance
    · apply digest_injective f hf
      calc
        PV_RunJoin_SpendDataMap.digest f (pub.change) =
            changeCommitment (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) := hchange
        _ = PV_RunJoin_SpendDataMap.digest f (changeCommitment pub w) := (map_changeCommitment f pub w).symm
  · intro h
    rcases h with ⟨hcanonical, hrelation, hbalance, hchange, hvariant, happend⟩
    have hvalue : f (w.inputValue.val : K) = (w.inputValue.val : L) := by simp
    refine ⟨(canonical_map_iff f hf pub).mpr hcanonical, ?_,
      ?_, ?_, (variantOutput_map_iff f hf pub w).mpr hvariant,
      (PV_RunJoin_AppendBindingMap.appendBinding_map_iff f pub).mpr happend⟩
    · have hm := (relation_map_iff f hf pub (w.inputValue.val : K) w.sk w.salt
        w.path w.pair).mpr hrelation
      simpa [PV_RunJoin_SpendDataMap.witness, hvalue] using hm
    · simpa [PV_RunJoin_SpendDataMap.witness] using hbalance
    · calc
        (PV_RunJoin_SpendDataMap.mapPublic f pub).change = PV_RunJoin_SpendDataMap.digest f pub.change := rfl
        _ = PV_RunJoin_SpendDataMap.digest f (changeCommitment pub w) := congrArg (PV_RunJoin_SpendDataMap.digest f) hchange
        _ = changeCommitment (PV_RunJoin_SpendDataMap.mapPublic f pub) (PV_RunJoin_SpendDataMap.witness f w) := map_changeCommitment f pub w

#print axioms canonical_map_iff
#print axioms rspend_map_iff

#print axioms map_eq_iff
#print axioms map_zero_iff
#print axioms digest_injective
#print axioms pair_valid_map_iff
#print axioms pair_spendable_map_iff
#print axioms canonical_map_iff
#print axioms map_digest_noteCommitment
#print axioms map_digest_ownerKey
#print axioms map_digest_nullifier
#print axioms map_digest_merkleRoot
#print axioms relation_map_iff
#print axioms map_changeCommitment
#print axioms map_recipientCommitment
#print axioms variantOutput_map_iff
#print axioms rspend_map_iff

end R1Z.PV_RunJoin_SpendRelationMap
