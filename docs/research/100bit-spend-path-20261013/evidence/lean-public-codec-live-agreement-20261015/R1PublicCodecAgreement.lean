import R1PublicByteCodec
import R1PublicIndexListCodec
import R1SemanticPublicWire
import R1PublicByteCodecLaws
import R1SemanticPublicByteBinding
import R1SemanticPublicWireSurjective

/-! Agreement between the compositional public codec and the existing
variant-indexed public wire model. These are Lean representation equalities;
source-parser refinement remains separate. -/
set_option autoImplicit false

namespace AspisR1.PublicCodecAgreement

open AspisR1.RetainedFieldByteCodec

private theorem append_ofFn4 (lo hi : Fin 4 → Byte) :
    List.ofFn lo ++ List.ofFn hi =
      List.ofFn (fun i : Fin 8 =>
        if h : i.val < 4 then lo ⟨i.val, h⟩ else hi ⟨i.val - 4, by omega⟩) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi8 : i < 8 := by simpa using hright
    by_cases h : i < 4 <;> simp [h]

theorem u64_emit_eq_index_encode (x : AspisR1.PublicIndexCodec.Index) :
    AspisR1.PublicByteCodec.u64Codec.emit x =
      AspisR1.PublicIndexListCodec.encode x := by
  let halves := AspisR1.PublicByteCodec.u64Equiv.symm x
  have hsplit := append_ofFn4
    (RetainedFieldByteCodec.encodeWordLE halves.1)
    (RetainedFieldByteCodec.encodeWordLE halves.2)
  have hlow : halves.1.val = x.val % RetainedFieldByteCodec.rawWordCount := rfl
  have hhigh : halves.2.val = x.val / RetainedFieldByteCodec.rawWordCount := rfl
  change (List.ofFn (RetainedFieldByteCodec.encodeWordLE halves.1) ++
      List.ofFn (RetainedFieldByteCodec.encodeWordLE halves.2)) =
    List.ofFn (AspisR1.PublicIndexCodec.encode x)
  rw [hsplit]
  apply congrArg List.ofFn
  funext i
  by_cases h : i.val < 4
  · simp only [AspisR1.PublicIndexCodec.encode, dif_pos h]
    change RetainedFieldByteCodec.encodeWordLE halves.1 ⟨i.val, h⟩ =
      RetainedFieldByteCodec.encodeWordLE
        ⟨x.val % RetainedFieldByteCodec.rawWordCount, by
          exact Nat.mod_lt _ (by norm_num [RetainedFieldByteCodec.rawWordCount])⟩
        ⟨i.val, h⟩
    rfl
  · simp only [AspisR1.PublicIndexCodec.encode, dif_neg h]
    change RetainedFieldByteCodec.encodeWordLE halves.2 ⟨i.val - 4, by omega⟩ =
      RetainedFieldByteCodec.encodeWordLE
        ⟨x.val / RetainedFieldByteCodec.rawWordCount, by
          have hx := x.isLt
          norm_num [RetainedFieldByteCodec.rawWordCount] at hx ⊢
          omega⟩
        ⟨i.val - 4, by omega⟩
    rfl

theorem encode_toPublic_eq_wire_encode (w : AspisR1.SemanticPublicWire.Wire) :
    AspisR1.PublicByteCodec.encode (AspisR1.SemanticPublicWire.toPublic w) =
      some (AspisR1.SemanticPublicWire.encode w) := by
  cases w with
  | transfer common recipient =>
      simp [AspisR1.PublicByteCodec.encode,
        AspisR1.PublicByteCodec.publicCodec,
        AspisR1.PublicByteCodec.publicFieldsEquiv,
        AspisR1.PublicByteCodec.toFields,
        AspisR1.PublicByteCodec.fieldsCodec,
        AspisR1.PublicByteCodec.PrefixCodec.transport,
        AspisR1.PublicByteCodec.PrefixCodec.pair,
        AspisR1.PublicByteCodec.PrefixCodec.fixed,
        AspisR1.PublicByteCodec.PrefixCodec.option,
        AspisR1.PublicByteCodec.variantCodec,
        AspisR1.PublicByteCodec.digestCodec,
        AspisR1.PublicByteCodec.m31Codec,
        AspisR1.PublicByteCodec.frontierCodec,
        AspisR1.PublicByteCodec.encodeFrontier,
        AspisR1.PublicByteCodec.encodeDigest,
        AspisR1.PublicFieldBlockCodec.encodeDigest,
        AspisR1.PublicFieldBlockCodec.encodeFields,
        AspisR1.PublicFieldBlockCodec.encodeFrontier,
        AspisR1.SemanticPublicWire.toPublic_index_bound,
        AspisR1.SemanticPublicWire.toPublic,
        AspisR1.SemanticPublicWire.encode,
        AspisR1.SemanticPublicWire.header,
        AspisR1.SemanticPublicWire.afterBytes,
        u64_emit_eq_index_encode]
      rfl
  | withdrawal common amount =>
      simp [AspisR1.PublicByteCodec.encode,
        AspisR1.PublicByteCodec.publicCodec,
        AspisR1.PublicByteCodec.publicFieldsEquiv,
        AspisR1.PublicByteCodec.toFields,
        AspisR1.PublicByteCodec.fieldsCodec,
        AspisR1.PublicByteCodec.PrefixCodec.transport,
        AspisR1.PublicByteCodec.PrefixCodec.pair,
        AspisR1.PublicByteCodec.PrefixCodec.fixed,
        AspisR1.PublicByteCodec.PrefixCodec.option,
        AspisR1.PublicByteCodec.variantCodec,
        AspisR1.PublicByteCodec.digestCodec,
        AspisR1.PublicByteCodec.m31Codec,
        AspisR1.PublicByteCodec.frontierCodec,
        AspisR1.PublicByteCodec.encodeFrontier,
        AspisR1.PublicByteCodec.encodeDigest,
        AspisR1.PublicFieldBlockCodec.encodeDigest,
        AspisR1.PublicFieldBlockCodec.encodeFields,
        AspisR1.PublicFieldBlockCodec.encodeFrontier,
        AspisR1.SemanticPublicWire.toPublic_index_bound,
        AspisR1.SemanticPublicWire.toPublic,
        AspisR1.SemanticPublicWire.encode,
        AspisR1.SemanticPublicWire.header,
        AspisR1.SemanticPublicWire.afterBytes,
        u64_emit_eq_index_encode]
      rfl

/-- Encoding checks only the u64 index bound. In particular, malformed option
shapes and zero withdrawals can be emitted, although checked parsing rejects
them. The wire carrier's total encoder has a smaller input type. -/
theorem encode_none_iff (pub : PublicByteCodec.BasePublic) :
    PublicByteCodec.encode pub = none ↔ ¬ pub.nextPairIndex < 2 ^ 64 := by
  unfold PublicByteCodec.encode
  split
  next hi =>
    constructor
    · intro h
      cases h
    · intro hn
      exact False.elim (hn hi)
  next hi =>
    exact ⟨fun _ => hi, fun _ => rfl⟩

theorem encode_exists_iff (pub : PublicByteCodec.BasePublic) :
    (∃ bytes, PublicByteCodec.encode pub = some bytes) ↔ pub.nextPairIndex < 2 ^ 64 := by
  constructor
  · rintro ⟨bytes, h⟩
    exact PublicByteCodec.encode_success_bound pub bytes h
  · intro hi
    exact ⟨PublicByteCodec.publicCodec.emit ⟨pub, hi⟩, by
      simp only [PublicByteCodec.encode, dif_pos hi]⟩

/-- Every public value and byte list is covered. The live checked wire parser
accepts exactly a compositional encoding whose option shape is canonical. -/
theorem parsePublic_eq_some_iff (bytes : PublicByteCodec.Bytes)
    (pub : PublicByteCodec.BasePublic) :
    SemanticPublicWire.parsePublic bytes = some pub ↔
      PublicByteCodec.encode pub = some bytes ∧ PublicOptionShape.canonical pub := by
  constructor
  · intro h
    obtain ⟨wire, hw, hb⟩ := SemanticPublicByteBinding.parsed_exact_bytes bytes pub h
    refine ⟨?_, SemanticPublicWire.parsePublic_canonical bytes pub h⟩
    rw [← hw, encode_toPublic_eq_wire_encode, hb]
  · rintro ⟨he, hc⟩
    obtain ⟨wire, hw⟩ := SemanticPublicWireSurjective.exists_wire pub hc
      (PublicByteCodec.encode_success_bound pub bytes he)
    have hs : PublicByteCodec.encode (SemanticPublicWire.toPublic wire) = some bytes := by
      simpa only [hw] using he
    have hb : SemanticPublicWire.encode wire = bytes :=
      Option.some.inj ((encode_toPublic_eq_wire_encode wire).symm.trans hs)
    have hwc : PublicOptionShape.canonical (SemanticPublicWire.toPublic wire) := by
      simpa only [hw] using hc
    rw [← hb, SemanticPublicWireRoundTrip.parsePublic_encode wire hwc, hw]

theorem encode_eq_some_iff_parsePublic (pub : PublicByteCodec.BasePublic)
    (bytes : PublicByteCodec.Bytes) (hc : PublicOptionShape.canonical pub) :
    PublicByteCodec.encode pub = some bytes ↔
      SemanticPublicWire.parsePublic bytes = some pub := by
  exact ⟨fun he => (parsePublic_eq_some_iff bytes pub).mpr ⟨he, hc⟩,
    fun hp => ((parsePublic_eq_some_iff bytes pub).mp hp).1⟩

/-- All-byte agreement includes every malformed, truncated and trailing input.
It compares checked parsers, so the common zero-withdrawal rejection is retained. -/
theorem decode_eq_parsePublic (bytes : PublicByteCodec.Bytes) :
    PublicByteCodec.decode bytes = SemanticPublicWire.parsePublic bytes := by
  apply Option.ext
  intro pub
  rw [PublicByteCodec.decode_eq_some_iff, parsePublic_eq_some_iff,
    PublicOptionShape.check_eq_true_iff]

/-- Directly supplies the live hpub premise without changing its consumer. -/
theorem parsePublic_of_decode (bytes : PublicByteCodec.Bytes)
    (pub : PublicByteCodec.BasePublic)
    (h : PublicByteCodec.decode bytes = some pub) :
    SemanticPublicWire.parsePublic bytes = some pub := by
  rw [← decode_eq_parsePublic]
  exact h

/-- Raw wire decoding permits zero: it is the checked parsers that reject it. -/
theorem zero_withdrawal_raw_decode (c : SemanticPublicWire.Common) :
    SemanticPublicWire.decode (SemanticPublicWire.encode (.withdrawal c 0)) =
      some (.withdrawal c 0) :=
  SemanticPublicWireRoundTrip.decode_encode (.withdrawal c 0)

theorem zero_withdrawal_checked_reject (c : SemanticPublicWire.Common) :
    SemanticPublicWire.parsePublic (SemanticPublicWire.encode (.withdrawal c 0)) = none ∧
      PublicByteCodec.decode (SemanticPublicWire.encode (.withdrawal c 0)) = none := by
  have hp : SemanticPublicWire.parsePublic
      (SemanticPublicWire.encode (.withdrawal c 0)) = none := by
    simp [SemanticPublicWire.parsePublic, SemanticPublicWireRoundTrip.decode_encode,
      SemanticPublicWire.toPublic, PublicOptionShape.check]
  exact ⟨hp, by rw [decode_eq_parsePublic, hp]⟩

#print axioms u64_emit_eq_index_encode
#print axioms encode_toPublic_eq_wire_encode
#print axioms encode_none_iff
#print axioms encode_exists_iff
#print axioms parsePublic_eq_some_iff
#print axioms encode_eq_some_iff_parsePublic
#print axioms decode_eq_parsePublic
#print axioms parsePublic_of_decode
#print axioms zero_withdrawal_raw_decode
#print axioms zero_withdrawal_checked_reject

end AspisR1.PublicCodecAgreement
