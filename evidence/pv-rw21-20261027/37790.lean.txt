import R1Z.ProverRw21EncodedSlice
import R1Z.ProverRw21SequenceImage
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21EncodedImage
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw21EncodedStep
variable [ExternalTypes]

theorem source (ops : ExternalFuns) (values : Slice W)
    (bound : 32*values.length≤Usize.max)
    (canonical : ∀ x∈values.val,ProverRw21WideCarrier.canonical x) :
    ∃ result, @prover.encoded_slice _ (selected ops) values=ok result ∧
      result.val.map ProverRw21ByteCarrier.decode = values.val.flatMap
        (fun x => ProverRw21ProtocolOutput.wide (ProverRw21WideCarrier.value x)) :=
  ⟨ProverRw21EncodedSlice.output values bound,ProverRw21EncodedSlice.source ops values bound,
    ProverRw21SequenceImage.image values.val canonical⟩

#print axioms source
end R1Z.ProverRw21EncodedImage
