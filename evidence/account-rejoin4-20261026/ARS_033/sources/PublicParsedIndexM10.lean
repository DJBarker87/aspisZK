import PublicParserWork

set_option autoImplicit false
namespace AspisR1.PublicParsedIndexM10
open AspisV8R15.ExactTowerBase

theorem bound (bytes : List PublicPrimitiveDecoderWork.Byte) (pub : R0P.Public M31Exact)
    (h : (PublicParserWork.parsePublic bytes).1 = some pub) : pub.nextPairIndex < 2^64 := by
  rw [PublicParserWork.parsePublic_value] at h
  cases hd : SemanticPublicWire.decode bytes with
  | none => simp [SemanticPublicWire.parsePublic,hd] at h
  | some wire =>
    simp only [SemanticPublicWire.parsePublic,hd] at h
    change (if PublicOptionShape.check (SemanticPublicWire.toPublic wire) = true
      then some (SemanticPublicWire.toPublic wire) else none) = some pub at h
    split at h
    · cases h
      exact SemanticPublicWire.toPublic_index_bound wire
    · cases h

#print axioms bound
end AspisR1.PublicParsedIndexM10
