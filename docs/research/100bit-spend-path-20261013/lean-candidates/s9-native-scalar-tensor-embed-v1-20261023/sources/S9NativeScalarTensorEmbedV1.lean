import S9NativeDecodedScalarProductV1
import S9ActualTensorArithmeticV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1S9NativeScalarTensorEmbedV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeDecodedScalarProductV1

/-- Existing native tensor and current-Wide decoders interpret the SAME four
source words. This is a coordinate-only identity, not arithmetic/Can. -/
theorem tensor_decode_current (q : NativeQ) :
    AspisR1CurrentWide.Proof.decodeQM (toCurrentQ q)=
      AspisR1S9ActualTensorArithmeticV1.decode q := by rfl

/-- Exact ring embedding requested by the common/tensor contraction: no
new embedding or encoded operand assumption is introduced. -/
theorem scalar_embed_tensor (q : NativeQ) :
    scalarEmbed q =
      algebraMap AspisR1CurrentWide.Proof.ExactQM AspisWideTower.WideExact
        (AspisR1S9ActualTensorArithmeticV1.decode q) := by
  unfold scalarEmbed
  rw [tensor_decode_current]

#print axioms tensor_decode_current
#print axioms scalar_embed_tensor
end AspisR1S9NativeScalarTensorEmbedV1
