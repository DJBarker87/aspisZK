import RPu_FJq_PublicOnPreparation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceLiteralPublic
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)
/-- A source serializer result and the literal parse of its SAME bytes identify
all public operands, independently of the omitted pool/domain observations. -/
theorem value (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (bytes : alloc.vec.Vec U8) (wire : SemanticPublicWire.Wire)
    (mapped : PublicSourceRaw.toWire (AspisR1TerminalDecoder.PublicBinding.projectRaw s)=some wire)
    (parsed : SemanticPublicWire.parsePublic (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte)=
      some (SemanticPublicWire.toPublic wire))
    (pubBytes : List SemanticPublicWire.Byte) (literalPub : R0P.Public SemanticPublicWire.M31)
    (sameBytes : pubBytes=bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte)
    (literal : SemanticPublicWire.parsePublic pubBytes=some literalPub) :
    SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native
      (PreparationBinding.preparationPublic s)))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub := by
  rw [sameBytes,parsed] at literal
  have same:=Option.some.inj literal
  rw [←same]
  exact FJq_PublicWire.value s wire mapped
#print axioms value
end AspisR1.FJq_SourceLiteralPublic
end
