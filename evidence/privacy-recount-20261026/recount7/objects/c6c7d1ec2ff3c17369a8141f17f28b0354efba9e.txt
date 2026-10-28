import R1Z.PV_RunJoin_PoseidonMap

/-! Ring-hom naturality for the R0 note-hash and 24-level Merkle functions.
These are algebraic transport lemmas only; they do not connect a runtime field
parser or a Rust trace to the generic semantic model. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NoteHashMap

open R0P R1Z.PV_RunJoin_PoseidonMap

variable {K L : Type} [Field K] [Field L] (f : K →+* L)

theorem map_spongeInit (domain len : K) :
    mapState f (spongeInit domain len) =
      spongeInit (f domain) (f len) := by
  funext lane
  by_cases h8 : lane = 8
  · subst lane
    simp [mapState, spongeInit]
  · by_cases h9 : lane = 9
    · subst lane
      simp [mapState, spongeInit, h8]
    · simp [mapState, spongeInit, h8, h9]

theorem map_absorb (s : State K) (chunk : R0P.Digest K) :
    mapState f (absorb s chunk) =
      absorb (mapState f s) (mapDigest f chunk) := by
  funext lane
  by_cases h : lane.val < 8 <;>
    simp [mapState, mapDigest, absorb, h, map_add]

theorem map_spongeStep (s : State K) (chunk : R0P.Digest K) :
    mapState f (spongeStep s chunk) =
      spongeStep (mapState f s) (mapDigest f chunk) := by
  unfold spongeStep
  rw [map_poseidonPermutation, map_absorb]

theorem map_digestOf (s : State K) :
    mapDigest f (digestOf s) = digestOf (mapState f s) := by
  rfl

theorem map_ownerKey (sk : R0P.Digest K) :
    mapDigest f (ownerKey sk) = ownerKey (mapDigest f sk) := by
  unfold ownerKey
  rw [map_digestOf, map_spongeStep, map_spongeInit]
  simp only [map_ofNat]

theorem map_nullifierHash (sk salt : R0P.Digest K) :
    mapDigest f (nullifierHash sk salt) =
      nullifierHash (mapDigest f sk) (mapDigest f salt) := by
  unfold nullifierHash
  rw [map_digestOf, map_spongeStep, map_spongeStep, map_spongeInit]
  simp only [map_ofNat]

theorem map_noteCommitment (pk : R0P.Digest K) (value asset : K)
    (salt : R0P.Digest K) :
    mapDigest f (noteCommitment pk value asset salt) =
      noteCommitment (mapDigest f pk) (f value) (f asset) (mapDigest f salt) := by
  unfold noteCommitment
  let chunk2K : R0P.Digest K := fun i =>
    if i.val = 0 then value else if i.val = 1 then asset
      else salt ⟨i.val - 2, by omega⟩
  let chunk2L : R0P.Digest L := fun i =>
    if i.val = 0 then f value else if i.val = 1 then f asset
      else mapDigest f salt ⟨i.val - 2, by omega⟩
  let chunk3K : R0P.Digest K := fun i =>
    if h : i.val < 2 then salt ⟨i.val + 6, by omega⟩ else 0
  let chunk3L : R0P.Digest L := fun i =>
    if h : i.val < 2 then mapDigest f salt ⟨i.val + 6, by omega⟩ else 0
  have hchunk2 : mapDigest f chunk2K = chunk2L := by
    funext i
    change f (chunk2K i) = chunk2L i
    fin_cases i <;> simp [chunk2K, chunk2L, mapDigest]
  have hchunk3 : mapDigest f chunk3K = chunk3L := by
    funext i
    change f (chunk3K i) = chunk3L i
    fin_cases i <;> simp [chunk3K, chunk3L, mapDigest]
  change mapDigest f
      (digestOf (spongeStep (spongeStep (spongeStep
        (spongeInit (0x4153_0003 : K) 18) pk) chunk2K) chunk3K)) = _
  rw [map_digestOf, map_spongeStep, map_spongeStep, map_spongeStep,
    map_spongeInit, hchunk2, hchunk3]
  simp only [map_ofNat, chunk2L, chunk3L]

def mapPath (path : Fin 24 → Bool × R0P.Digest K) :
    Fin 24 → Bool × R0P.Digest L :=
  fun level => ((path level).1, mapDigest f (path level).2)

theorem map_merkleStep (cur : R0P.Digest K) (bit : Bool)
    (sibling : R0P.Digest K) :
    mapDigest f (merkleStep cur bit sibling) =
      merkleStep (mapDigest f cur) bit (mapDigest f sibling) := by
  cases bit <;> simp [merkleStep, map_nodeCompress]

theorem map_merkleRootAux (cur : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) :
    ∀ n, mapDigest f (merkleRootAux cur path n) =
      merkleRootAux (mapDigest f cur) (mapPath f path) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold merkleRootAux
      by_cases h : n < 24
      · simp only [dif_pos h]
        rw [map_merkleStep, ih]
        simp [mapPath]
      · simp only [dif_neg h]
        exact ih

theorem map_merkleRoot (leaf : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) :
    mapDigest f (merkleRoot leaf path) =
      merkleRoot (mapDigest f leaf) (mapPath f path) := by
  unfold merkleRoot
  exact map_merkleRootAux f leaf path 24

#print axioms map_spongeInit
#print axioms map_absorb
#print axioms map_spongeStep
#print axioms map_digestOf
#print axioms map_ownerKey
#print axioms map_nullifierHash
#print axioms map_noteCommitment
#print axioms map_merkleStep
#print axioms map_merkleRootAux
#print axioms map_merkleRoot

#print axioms map_spongeInit
#print axioms map_absorb
#print axioms map_spongeStep
#print axioms map_digestOf
#print axioms map_ownerKey
#print axioms map_nullifierHash
#print axioms map_noteCommitment
#print axioms map_merkleStep
#print axioms map_merkleRootAux
#print axioms map_merkleRoot

end R1Z.PV_RunJoin_NoteHashMap
