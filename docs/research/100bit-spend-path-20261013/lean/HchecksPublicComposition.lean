import ExtractedAdapterStageBindingObligations
import R1LiteralTranscript

/-! Public-field adapter for R16. The actual serialized argument, guard,
supplied-public binding and equality to the literal public remain explicit. -/
set_option autoImplicit false
namespace AspisR1.HchecksPublicComposition
open AspisR1AdapterReconstruct.StageBinding
open AspisR1PublicSerializer

theorem publicParsed_of_serializer
    (stage1 : Whole431.Public) (bytes : FieldsRefinement431.ByteVec)
    (pub : LiteralTranscript.Public) (decoded : R0P.Public SemanticPublicWire.M31)
    (hs : SerializerWitness stage1 bytes) (hguard : PaymentGuard stage1)
    (hbind : SuppliedPublicBinding stage1 decoded)
    (hbytes : pub.pubBytes = bytes.val.map RawBridge431.rawByte) :
    SemanticPublicWire.parsePublic pub.pubBytes = some decoded := by
  rw [hbytes]
  exact serializer_supplied_public stage1 bytes decoded hs hguard hbind

#print axioms publicParsed_of_serializer
end AspisR1.HchecksPublicComposition
