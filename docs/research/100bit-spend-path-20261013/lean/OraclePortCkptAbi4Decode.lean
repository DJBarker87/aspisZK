import OraclePortCkptAbi2Extracted.Funs
import OraclePortCkptAbi3Canonical

/-! Canonicality comes from successful extracted strict decoding, not from
an arbitrary raw writer state. This is a local reference-decoder theorem. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.OraclePortCkptAbi4Decode
open OraclePortCkptAbi2Extracted
abbrev RawK := aspis_core.field.QM31

def Canonical (q : RawK) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

#print Aeneas.Std.Array.index_usize
#print Aeneas.Std.Result

/-- No byte-length or caller canonicality hypothesis: every successful
strict decoder result has four canonical raw limbs. -/
theorem decoded_canonical (b : Slice U8) (q : RawK)
    (success : decode_k_spec b = ok (some q)) : Canonical q := by
  unfold decode_k_spec at success
  cases h0 : word_spec b 0#usize <;> simp_all
  cases h1 : word_spec b 4#usize <;> simp_all
  cases h2 : word_spec b 8#usize <;> simp_all
  cases h3 : word_spec b 12#usize <;> simp_all
  simp only [Array.index_usize, k_from_limbs] at success
  simp at success
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  subst q
  simp only [Canonical]
  omega

def CanonicalWide (q : aspis_core.field.wide_exact.WideExact) : Prop :=
  Canonical q.c0 ∧ Canonical q.c1

/-- The actual extracted wide constructor admits only canonical limbs. -/
theorem from_limbs_canonical (a : Array U32 8#usize)
    (q : aspis_core.field.wide_exact.WideExact)
    (success : aspis_core.field.wide_exact.WideExact.from_limbs a = ok (some q)) :
    CanonicalWide q := by
  unfold aspis_core.field.wide_exact.WideExact.from_limbs at success
  simp only [Array.index_usize, aspis_core.field.P] at success
  simp at success
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  subst q
  simp only [CanonicalWide,Canonical]
  omega

/-- All eight strict wide reads feed the checked constructor; success entails
canonicality without an external assumption about the byte slice. -/
theorem decoded_wide_canonical (b : Slice U8)
    (q : aspis_core.field.wide_exact.WideExact)
    (success : decode_e_spec b = ok (some q)) : CanonicalWide q := by
  unfold decode_e_spec at success
  dsimp only at success
  split at success
  · cases success
  · cases h0 : word_spec b 0#usize <;> simp_all
    cases h1 : word_spec b 4#usize <;> simp_all
    cases h2 : word_spec b 8#usize <;> simp_all
    cases h3 : word_spec b 12#usize <;> simp_all
    cases h4 : word_spec b 16#usize <;> simp_all
    cases h5 : word_spec b 20#usize <;> simp_all
    cases h6 : word_spec b 24#usize <;> simp_all
    cases h7 : word_spec b 28#usize <;> simp_all
    exact from_limbs_canonical _ q success

def words (q : RawK) : List Nat :=
  [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]

/-- The full four-word byte projection survives the exact-field quotient
for strict decoded values. This does not yet identify encode_k or C5.encodeK. -/
theorem canonical_words_bytes (q : RawK) (h : Canonical q) :
    (words q).flatMap OraclePortCompactDraft.le32 =
      (words q).flatMap (fun n : Nat => OraclePortCompactDraft.le32
        (n : ZMod 2147483647).val) := by
  obtain ⟨h0,h1,h2,h3⟩ := h
  simp only [words,List.flatMap_cons,List.flatMap_nil,
    OraclePortCkptAbi3Canonical.canonical_word_bytes _ h0,
    OraclePortCkptAbi3Canonical.canonical_word_bytes _ h1,
    OraclePortCkptAbi3Canonical.canonical_word_bytes _ h2,
    OraclePortCkptAbi3Canonical.canonical_word_bytes _ h3]

#print axioms decoded_wide_canonical
#print axioms canonical_words_bytes

#print axioms from_limbs_canonical

#print axioms decoded_canonical
end AspisR1.OraclePortCkptAbi4Decode
