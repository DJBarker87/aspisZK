import PublicRawCore
import R1PublicSourceRawSuccess

/-! Agreement of the existing R1 raw serializer with the shared pure core.
This Lean4.32 theorem does not import or replay the separate Lean4.31 Aeneas
proof. It leaves existing raw serializer definitions unchanged. -/
set_option autoImplicit false
namespace AspisR1.PublicRawCoreAgreement
open PublicSourceRaw

def toCoreCommon (c : Common) : PublicRawCore.Common :=
  { anchor := c.anchor, nullifier := c.nullifier, assetId := c.assetId,
    change := c.change, nextPairIndex := c.nextPairIndex,
    snapshotFrontier := c.snapshotFrontier, nextRoot := c.nextRoot,
    nextFrontier := c.nextFrontier }

def toCore : Public → PublicRawCore.Public
  | .transfer c recipient => .transfer (toCoreCommon c) recipient
  | .withdrawal c amount => .withdrawal (toCoreCommon c) amount

theorem wordByte_eq (x : Word) (i : Fin 4) :
    RetainedFieldByteCodec.encodeWordLE x i = PublicRawCore.wordByte x i := by
  fin_cases i <;> rfl

theorem wordBytes_eq (x : Word) : wordBytes x = PublicRawCore.wordBytes x := by
  unfold wordBytes PublicRawCore.wordBytes
  congr 1
  funext i
  exact wordByte_eq x i

theorem indexBytes_eq (x : PublicIndexCodec.Index) :
    PublicIndexListCodec.encode x = PublicRawCore.indexBytes x := by
  unfold PublicIndexListCodec.encode PublicRawCore.indexBytes
  congr 1
  funext i
  unfold PublicIndexCodec.encode PublicRawCore.indexByte
  split <;> apply wordByte_eq

theorem canonical_iff (p : Public) : Canonical p ↔ PublicRawCore.Canonical (toCore p) := by
  cases p <;>
    simp [Canonical, commonCanonical, fieldCanonical, RetainedFieldByteCodec.m31Modulus,
      RetainedFieldByteCodec.rawCandidateCount, PublicRawCore.Canonical, toCore,
      toCoreCommon, PublicRawCore.words, PublicRawCore.headerWords,
      PublicRawCore.afterWords, PublicRawCore.frontierWords, PublicRawCore.digestWords,
      List.mem_flatMap, List.mem_ofFn] <;> tauto

theorem fields_canonical (xs : List Word) (h : ∀ x ∈ xs, fieldCanonical x) :
    fields xs = some (PublicRawCore.encodeWords xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : fieldCanonical x := h x (by simp)
      have ht : ∀ y ∈ xs, fieldCanonical y := by intro y hy; exact h y (by simp [hy])
      simp only [fields, if_pos hx, ih ht, Option.map_some, wordBytes_eq,
        PublicRawCore.encodeWords, List.flatMap_cons]

theorem digest_canonical (d : Digest) (h : ∀ i, fieldCanonical (d i)) :
    digestBytes d = some (PublicRawCore.encodeWords (PublicRawCore.digestWords d)) := by
  apply fields_canonical
  simpa using h

theorem digests_canonical (ds : List Digest) (h : ∀ d ∈ ds, ∀ i, fieldCanonical (d i)) :
    digests ds = some (PublicRawCore.encodeWords (ds.flatMap PublicRawCore.digestWords)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      have hd : ∀ i, fieldCanonical (d i) := h d (by simp)
      have ht : ∀ e ∈ ds, ∀ i, fieldCanonical (e i) := by
        intro e he; exact h e (by simp [he])
      simp [digests, digest_canonical d hd, ih ht, PublicRawCore.encodeWords,
        List.flatMap_append]

theorem frontier_canonical (f : Frontier) (h : ∀ l i, fieldCanonical (f l i)) :
    frontierBytes f = some (PublicRawCore.encodeWords (PublicRawCore.frontierWords f)) := by
  apply digests_canonical
  simpa using h

theorem header_canonical (c : Common) (h : commonCanonical c) :
    header c = some (PublicRawCore.encodeWords (PublicRawCore.headerWords (toCoreCommon c))) := by
  have ha := digest_canonical c.anchor h.1
  have hn := digest_canonical c.nullifier h.2.1
  have hx := fields_canonical [c.assetId] (by simpa using h.2.2.1)
  simp [header, ha, hn, hx, PublicRawCore.headerWords, PublicRawCore.encodeWords,
    toCoreCommon, List.flatMap_append]

theorem after_canonical (c : Common) (h : commonCanonical c) :
    afterBytes c = some (PublicRawCore.afterBytes (toCoreCommon c)) := by
  have hs := frontier_canonical c.snapshotFrontier h.2.2.2.2.1
  have hr := digest_canonical c.nextRoot h.2.2.2.2.2.1
  have hn := frontier_canonical c.nextFrontier h.2.2.2.2.2.2
  simp [afterBytes, hs, hr, hn, indexBytes_eq, PublicRawCore.afterBytes,
    PublicRawCore.afterWords, PublicRawCore.encodeWords, toCoreCommon,
    List.flatMap_append, List.append_assoc]

theorem serialize_canonical (p : Public) (h : Canonical p) :
    serialize p = some (PublicRawCore.encode (toCore p)) := by
  cases p with
  | transfer c recipient =>
      have hc := h.1
      have hr := digest_canonical recipient h.2
      have hch := digest_canonical c.change hc.2.2.2.1
      simp [serialize, header_canonical c hc, hr, hch, after_canonical c hc,
        PublicRawCore.encode, toCore, toCoreCommon]
  | withdrawal c amount =>
      have hc := h.1
      have hm := fields_canonical [amount] (by simpa using h.2)
      have hch := digest_canonical c.change hc.2.2.2.1
      simp [serialize, header_canonical c hc, hm, hch, after_canonical c hc,
        PublicRawCore.encode, toCore, toCoreCommon]

theorem serialize_eq (p : Public) : serialize p = PublicRawCore.serialize (toCore p) := by
  by_cases h : Canonical p
  · rw [serialize_canonical p h]
    simp [PublicRawCore.serialize, (canonical_iff p).mp h]
  · have hn : serialize p = none := by
      cases hs : serialize p with
      | none => rfl
      | some bytes => exact False.elim (h (PublicSourceRawSuccess.serialize_success_canonical p bytes hs))
    rw [hn]
    simp [PublicRawCore.serialize, ← canonical_iff p, h]

#print axioms wordBytes_eq
#print axioms indexBytes_eq
#print axioms canonical_iff
#print axioms serialize_canonical
#print axioms serialize_eq
end AspisR1.PublicRawCoreAgreement
