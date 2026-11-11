import RPv_FJq_PublicOnPreparation
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): STATEMENT CHANGE in the public-model side only:
`FIw_PublicModel.ofPublic` now takes the PIN2 `PIN2P.SemanticPublic` (W3c), so it is applied
to `PIN2W11_PublicCopy.nativePIN2` (release `FJa_PublicCopy.native` plus the PIN2
`destination`) of the same preparation public.  The model therefore also carries pool,
deployment domain and the withdrawal destination, matching W3a's wire parse.  Premises and
proof text unchanged (`FJq_PublicNative.value` restated the same way). -/
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
    SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (PIN2W11_PublicCopy.nativePIN2
      (PreparationBinding.preparationPublic s)))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub := by
  rw [sameBytes,parsed] at literal
  have same:=Option.some.inj literal
  rw [←same]
  exact FJq_PublicWire.value s wire mapped
#print axioms value
end AspisR1.FJq_SourceLiteralPublic
end
