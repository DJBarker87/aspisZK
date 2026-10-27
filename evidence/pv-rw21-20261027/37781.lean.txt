import R1Z.ProverRw21WideImage
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21WideEncoded
open Aeneas Aeneas.Std Result ProverRwFull ProverRw21WideCarrier

theorem image (x : E) :
    (ProverRw21FlatOutput.bytes (encode x)).map ProverRw21ByteCarrier.decode =
      ProverRw21ProtocolOutput.wide x := by
  rw [ProverRw21WideImage.mathematical_image (encode x) (canonical_encode x),value_encode]

theorem bytes (x : E) : ProverRw21FlatOutput.bytes (encode x) =
    (ProverRw21ProtocolOutput.wide x).map ProverRw19MathematicalAssembly.byte := by
  rw [← image x,ProverRw21ByteCarrier.encode_decode_list]

def output (x : E) : Array U8 32#usize :=
  ⟨(ProverRw21ProtocolOutput.wide x).map ProverRw19MathematicalAssembly.byte,by
    rw [← bytes x,ProverRw21FlatOutput.length];rfl⟩

theorem source (x : E) :
    ProverRwP6FlatSource.wide_bytes_flat (encode x)=ok (output x) := by
  rw [ProverRw21FlatSourceLaw.exact]
  congr 1
  apply Subtype.ext
  exact bytes x

#print axioms image
#print axioms bytes
#print axioms output
#print axioms source
end R1Z.ProverRw21WideEncoded
