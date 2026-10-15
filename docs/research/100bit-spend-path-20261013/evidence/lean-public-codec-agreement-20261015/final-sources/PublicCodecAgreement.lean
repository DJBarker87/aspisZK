import R1PublicByteCodec
import R1PublicIndexListCodec
import R1SemanticPublicWire

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

#print axioms u64_emit_eq_index_encode
#print axioms encode_toPublic_eq_wire_encode

end AspisR1.PublicCodecAgreement
