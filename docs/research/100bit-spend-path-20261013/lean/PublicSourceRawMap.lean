import R1PublicSourceRaw
import R1PublicCodecAgreement
import R1PublicByteCodecLaws

/-! PROPOSED, not yet compiled. Concrete raw-u32 mapping and serializer-model
agreement. No theorem in this module identifies handwritten `serialize` with
Rust execution. The source boundary is explicit in PublicSourceBoundary. -/
set_option autoImplicit false
namespace AspisR1.PublicSourceRawMap

open PublicSourceRaw

theorem rawField_canonical (x : M31) : fieldCanonical (rawField x) :=
  (RetainedExactLimbCodec.m31ResidueEquiv.symm x).isLt

theorem rawField_mapField (x : Word) (h : fieldCanonical x) :
    rawField (mapField x h) = x := by
  rw [rawField, mapField, RetainedExactLimbCodec.m31ResidueEquiv.symm_apply_apply]
  apply Fin.ext
  rfl

theorem rawField_zero : rawField (0 : M31) = 0 := by
  apply Fin.ext
  change (RetainedExactLimbCodec.m31ResidueEquiv.symm (0 : M31)).val = 0
  exact congrArg Fin.val (map_zero RetainedExactLimbCodec.m31ResidueEquiv.symm)

theorem mapField_ne_zero (x : Word) (h : fieldCanonical x) (hn : x.val ≠ 0) :
    mapField x h ≠ 0 := by
  intro hz
  have hx : x = 0 := by
    simpa only [rawField_mapField, rawField_zero] using congrArg rawField hz
  exact hn (congrArg Fin.val hx)

theorem rawCommon_mapCommon (c : Common) (h : commonCanonical c) :
    rawCommon (mapCommon c h) = c := by
  cases c
  dsimp only [rawCommon, mapCommon, PublicSourceRaw.rawFrontier, PublicSourceRaw.rawDigest]
  simp only [rawField_mapField]

theorem rawPublic_mapPublic (p : Public) (h : Canonical p) :
    rawPublic (mapPublic p h) = p := by
  cases p <;>
    dsimp only [mapPublic, rawPublic, PublicSourceRaw.rawDigest] <;>
    simp only [rawCommon_mapCommon, rawField_mapField]

theorem toWire_reifies (p : Public) (wire : SemanticPublicWire.Wire)
    (h : toWire p = some wire) : rawPublic wire = p := by
  unfold toWire at h
  split at h
  next hc =>
    have hw := Option.some.inj h
    rw [← hw]
    exact rawPublic_mapPublic p hc
  next hc => simp at h

theorem wordBytes_rawField (x : M31) : wordBytes (rawField x) = ExactLeafFieldCodec.encodeM31 x :=
  rfl

theorem fields_rawFields (xs : List M31) :
    fields (xs.map rawField) = some (xs.flatMap ExactLeafFieldCodec.encodeM31) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, fields, if_pos (rawField_canonical x), ih,
        Option.map_some, List.flatMap_cons, wordBytes_rawField]

theorem fields_rawField (x : M31) : fields [rawField x] = some (ExactLeafFieldCodec.encodeM31 x) := by
  simpa using fields_rawFields [x]

theorem digestBytes_rawDigest (d : SemanticPublicWire.Digest) :
    digestBytes (rawDigest d) = some (PublicFieldBlockCodec.encodeDigest d) := by
  change fields (List.ofFn (fun i => rawField (d i))) =
    some ((List.ofFn d).flatMap ExactLeafFieldCodec.encodeM31)
  simpa only [List.map_ofFn, Function.comp_def] using fields_rawFields (List.ofFn d)

theorem digests_rawDigests (ds : List SemanticPublicWire.Digest) :
    digests (ds.map rawDigest) = some (ds.flatMap PublicFieldBlockCodec.encodeDigest) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp [digests, digestBytes_rawDigest, ih]

theorem frontierBytes_rawFrontier (f : SemanticPublicWire.Frontier) :
    frontierBytes (rawFrontier f) = some (PublicFieldBlockCodec.encodeFrontier f) := by
  change digests (List.ofFn (fun l => rawDigest (f l))) =
    some ((List.ofFn f).flatMap PublicFieldBlockCodec.encodeDigest)
  simpa only [List.map_ofFn, Function.comp_def] using digests_rawDigests (List.ofFn f)

theorem header_rawCommon (c : SemanticPublicWire.Common) :
    header (rawCommon c) = some (SemanticPublicWire.header c) := by
  simp [header, rawCommon, digestBytes_rawDigest, fields_rawField, SemanticPublicWire.header]

theorem afterBytes_rawCommon (c : SemanticPublicWire.Common) :
    afterBytes (rawCommon c) = some (SemanticPublicWire.afterBytes c) := by
  simp [afterBytes, rawCommon, frontierBytes_rawFrontier, digestBytes_rawDigest,
    SemanticPublicWire.afterBytes]

theorem changeBytes_rawCommon (c : SemanticPublicWire.Common) :
    digestBytes (rawCommon c).change = some (PublicFieldBlockCodec.encodeDigest c.change) :=
  digestBytes_rawDigest c.change

theorem serialize_rawPublic (wire : SemanticPublicWire.Wire) :
    serialize (rawPublic wire) = some (SemanticPublicWire.encode wire) := by
  cases wire <;> simp [serialize, rawPublic, header_rawCommon, digestBytes_rawDigest,
    fields_rawField, afterBytes_rawCommon, changeBytes_rawCommon, SemanticPublicWire.encode]

theorem serialize_of_toWire (p : Public) (wire : SemanticPublicWire.Wire)
    (h : toWire p = some wire) : serialize p = some (SemanticPublicWire.encode wire) := by
  rw [← toWire_reifies p wire h]
  exact serialize_rawPublic wire

theorem mapPublic_canonical (p : Public) (hc : Canonical p)
    (hn : NonzeroWithdrawal p) : PublicOptionShape.canonical (SemanticPublicWire.toPublic (mapPublic p hc)) := by
  cases p with
  | transfer c recipient =>
      simp [mapPublic, SemanticPublicWire.toPublic, PublicOptionShape.canonical]
  | withdrawal c amount =>
      have hm := mapField_ne_zero amount hc.2 hn
      simp [mapPublic, SemanticPublicWire.toPublic, PublicOptionShape.canonical, hm]

theorem mapped_canonical (p : Public) (wire : SemanticPublicWire.Wire)
    (h : toWire p = some wire) (hn : NonzeroWithdrawal p) :
    PublicOptionShape.canonical (SemanticPublicWire.toPublic wire) := by
  unfold toWire at h
  split at h
  next hc =>
    have hw := Option.some.inj h
    rw [← hw]
    exact mapPublic_canonical p hc hn
  next hc => simp at h

theorem nonzero_of_payment_guard (p : Public) (h : PaymentAmountGuard p) : NonzeroWithdrawal p := by
  cases p with
  | transfer c recipient => trivial
  | withdrawal c amount => exact Nat.ne_of_gt h.1

/-- Concrete relation on every serialized coordinate, independent of bytes. -/
def RustPublicRel (source : Public) (pub : R0P.Public M31) : Prop :=
  ∃ wire, toWire source = some wire ∧ SemanticPublicWire.toPublic wire = pub

theorem encode_of_serialize (source : Public) (pub : R0P.Public M31) (bytes : Bytes)
    (hser : serialize source = some bytes) (hrel : RustPublicRel source pub) :
    PublicByteCodec.encode pub = some bytes := by
  obtain ⟨wire, hmap, hpub⟩ := hrel
  have hb : SemanticPublicWire.encode wire = bytes :=
    Option.some.inj ((serialize_of_toWire source wire hmap).symm.trans hser)
  rw [← hpub, ← hb]
  exact PublicCodecAgreement.encode_toPublic_eq_wire_encode wire

theorem decode_of_serialize (source : Public) (pub : R0P.Public M31) (bytes : Bytes)
    (hser : serialize source = some bytes) (hrel : RustPublicRel source pub)
    (hn : NonzeroWithdrawal source) : PublicByteCodec.decode bytes = some pub := by
  have hc : PublicOptionShape.canonical pub := by
    obtain ⟨wire, hmap, hpub⟩ := hrel
    rw [← hpub]
    exact mapped_canonical source wire hmap hn
  exact PublicByteCodec.decode_of_encode pub bytes (encode_of_serialize source pub bytes hser hrel) hc

#print axioms rawField_mapField
#print axioms toWire_reifies
#print axioms serialize_rawPublic
#print axioms serialize_of_toWire
#print axioms mapped_canonical
#print axioms encode_of_serialize
#print axioms decode_of_serialize
end AspisR1.PublicSourceRawMap
