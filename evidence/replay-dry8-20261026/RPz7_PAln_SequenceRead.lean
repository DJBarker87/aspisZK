import RPz7_PAln_LowRead
import R1SelectedFieldSequenceCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_SequenceRead
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open SelectedFieldSequenceCodec MultiproofConeCanonicalAppend

theorem wide_encode_exists (n : Nat) (b : Bytes) (length : b.length=32*n)
    (checked : canonical b) : ∃ values : Fin n → FoldedLeafCodec.Wide,
      encodeWide values=b := by
  induction n generalizing b with
  | zero =>
    have empty : b=[] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨Fin.elim0,empty.symm⟩
  | succ n ih =>
    have enough : 32≤b.length := by omega
    have firstlen : (b.take 32).length=32 := by simp only [List.length_take,Nat.min_eq_left enough]
    have tailLen : (b.drop 32).length=32*n := by simp only [List.length_drop];omega
    have parts := (canonical_take_drop b 32 (by decide) enough).mp checked
    obtain ⟨first,parsed⟩ := PAln_FieldRead.wide_exists (b.take 32) firstlen parts.1
    have firsteq := FoldedLeafCodec.encodeWide_of_decode _ first parsed
    obtain ⟨tail,taileq⟩ := ih (b.drop 32) tailLen parts.2
    refine ⟨Fin.cons first tail,?_⟩
    change FixedWidthDecoder.encode FoldedLeafCodec.encodeWide (Fin.cons first tail)=b
    simp only [FixedWidthDecoder.encode,List.ofFn_succ,List.flatMap_cons,Fin.cons_zero,Fin.cons_succ]
    rw [firsteq,show List.flatMap FoldedLeafCodec.encodeWide (List.ofFn tail)=b.drop 32 from taileq]
    exact List.take_append_drop _ _

theorem low_encode_exists (n : Nat) (b : Bytes) (length : b.length=16*n)
    (checked : canonical b) : ∃ values : Fin n → SemanticCoefficientCodec.LowWide,
      encodeLow values=expand n b := by
  induction n generalizing b with
  | zero => exact ⟨Fin.elim0,rfl⟩
  | succ n ih =>
    have enough : 16≤b.length := by omega
    have firstlen : (b.take 16).length=16 := by simp only [List.length_take,Nat.min_eq_left enough]
    have tailLen : (b.drop 16).length=16*n := by simp only [List.length_drop];omega
    have parts := (canonical_take_drop b 16 (by decide) enough).mp checked
    obtain ⟨first,parsed⟩ := PAln_LowRead.low_exists (b.take 16) firstlen parts.1
    have firsteq := SemanticCoefficientCodec.encodeLow_of_decode _ first parsed
    obtain ⟨tail,taileq⟩ := ih (b.drop 16) tailLen parts.2
    refine ⟨Fin.cons first tail,?_⟩
    rw [MultiproofConeExpandModel.expand_step]
    change FixedWidthDecoder.encode SemanticCoefficientCodec.encodeLow (Fin.cons first tail)=_
    simp only [FixedWidthDecoder.encode,List.ofFn_succ,List.flatMap_cons,Fin.cons_zero,Fin.cons_succ]
    rw [firsteq,show List.flatMap SemanticCoefficientCodec.encodeLow (List.ofFn tail)=expand n (b.drop 16) from taileq]

theorem wide_read_exists (n : Nat) (b : Bytes) (length : b.length=32*n)
    (checked : canonical b) : ∃ values, decodeWide n b=some values := by
  obtain ⟨values,encoded⟩ := wide_encode_exists n b length checked
  exact ⟨values,encoded ▸ decodeWide_encode values⟩

theorem low_read_exists (n : Nat) (b : Bytes) (length : b.length=16*n)
    (checked : canonical b) : ∃ values, decodeLow n (expand n b)=some values := by
  obtain ⟨values,encoded⟩ := low_encode_exists n b length checked
  exact ⟨values,encoded ▸ decodeLow_encode values⟩

#print axioms wide_encode_exists
#print axioms low_encode_exists
#print axioms wide_read_exists
#print axioms low_read_exists
end AspisR1.PAln_SequenceRead
end
