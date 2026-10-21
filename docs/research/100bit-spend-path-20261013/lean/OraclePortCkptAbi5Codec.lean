import OraclePortCkptAbi4Decode

/-! Canonical raw-to-exact byte representation. These laws concern the
extracted reference fields and C5; they do not adopt the production reader. -/
set_option autoImplicit false
namespace AspisR1.OraclePortCkptAbi5Codec
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi4Decode
open RetainedFieldByteCodec RetainedExactLimbCodec OraclePortCompactDraft

def limbs (q : RawK) (h : Canonical q) : QM31Limbs :=
  ![⟨q.c0.a.val,h.1⟩,⟨q.c0.b.val,h.2.1⟩,
    ⟨q.c1.a.val,h.2.2.1⟩,⟨q.c1.b.val,h.2.2.2⟩]

def exactK (q : RawK) (h : Canonical q) : OraclePortCheckpointAbiC5.K :=
  qm31ExactLimbEquiv (limbs q h)

/-- Four raw words, in emitted field order, give precisely C5's bytes when
strict decoding has established their canonical bounds. -/
theorem c5_k_bytes (q : RawK) (h : Canonical q) :
    OraclePortCheckpointAbiC5.encodeK (exactK q h) = (words q).flatMap le32 := by
  change List.ofFn (encodeQM31LE (qm31ExactLimbEquiv.symm
    (qm31ExactLimbEquiv (limbs q h)) )) = _
  rw [Equiv.symm_apply_apply]
  apply List.ext_getElem
  · simp only [List.length_ofFn,words,List.flatMap_cons,List.flatMap_nil,
      List.length_append,List.length_nil,le32,List.length_map,List.length_range]
  · intro i hi hj
    have bound : i < 16 := by simpa only [List.length_ofFn] using hi
    have index : i = (⟨i,bound⟩ : Fin 16).val := rfl
    revert hi hj
    rw [index]
    generalize (⟨i,bound⟩ : Fin 16) = j
    fin_cases j <;> intro hi hj <;> try rfl
    all_goals
      apply Fin.ext
      change _ % 256 = _ / 1 % 256
      rw [Nat.div_one]
      rfl

/-- C5's wide codec is the ordered concatenation of its two K codecs. -/
theorem c5_wide_halves (x : OraclePortCheckpointAbiC5.E) :
    OraclePortCheckpointAbiC5.encodeE x =
      OraclePortCheckpointAbiC5.encodeK x.re ++ OraclePortCheckpointAbiC5.encodeK x.im := by
  simp only [OraclePortCheckpointAbiC5.encodeE,FoldedLeafCodec.encodeWide,
    WideExactLimbCodec.pairExactEquiv,StrictWideByteCodec.encodeWideLE]
  rw [List.ofFn_add]
  rfl

def exactE (q : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact)
    (h : CanonicalWide q) : OraclePortCheckpointAbiC5.E :=
  WideExactLimbCodec.pairExactEquiv (limbs q.c0 h.1,limbs q.c1 h.2)

theorem c5_e_bytes (q : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact)
    (h : CanonicalWide q) :
    OraclePortCheckpointAbiC5.encodeE (exactE q h) =
      (words q.c0 ++ words q.c1).flatMap le32 := by
  rw [c5_wide_halves]
  change OraclePortCheckpointAbiC5.encodeK (exactK q.c0 h.1) ++
    OraclePortCheckpointAbiC5.encodeK (exactK q.c1 h.2) = _
  rw [c5_k_bytes,c5_k_bytes,List.flatMap_append]

/-- The caller need only supply success of the strict extracted decoder;
its canonicality proof is derived here. Actual reader adoption is separate. -/
theorem decoded_k_bytes (b : Slice U8) (q : RawK)
    (success : OraclePortCkptAbi2Extracted.decode_k_spec b = ok (some q)) :
    OraclePortCheckpointAbiC5.encodeK (exactK q (decoded_canonical b q success)) =
      (words q).flatMap le32 :=
  c5_k_bytes q (decoded_canonical b q success)

theorem decoded_e_bytes (b : Slice U8)
    (q : OraclePortCkptAbi2Extracted.aspis_core.field.wide_exact.WideExact)
    (success : OraclePortCkptAbi2Extracted.decode_e_spec b = ok (some q)) :
    OraclePortCheckpointAbiC5.encodeE (exactE q (decoded_wide_canonical b q success)) =
      (words q.c0 ++ words q.c1).flatMap le32 :=
  c5_e_bytes q (decoded_wide_canonical b q success)

#print Aeneas.Std.core.num.U32.to_le_bytes
#print Aeneas.Std.core.slice.Slice.copy_from_slice
#print Aeneas.Std.Array.to_slice_mut
#print axioms c5_e_bytes
#print axioms decoded_k_bytes
#print axioms decoded_e_bytes
#print axioms c5_k_bytes
#print axioms c5_wide_halves
end AspisR1.OraclePortCkptAbi5Codec
