import R1Z.ProverRw21EncodedTransport
import R1Z.ProverRwP6BodyStore
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21InstalledImage
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem flat (ops : ExternalFuns) :
    (ProverRwP6BodyStore.selected ops).op51=ProverRwP6FlatSource.wide_bytes_flat := rfl

theorem source (ops : ExternalFuns) (values : Slice ProverRw21FlatOutput.W)
    (bound : 32*values.length≤Usize.max) :
    @prover.encoded_slice _ (ProverRwP6BodyStore.selected ops) values=
      ok (ProverRw21EncodedSlice.output values bound) :=
  ProverRw21EncodedTransport.source _ (flat ops) values bound

theorem image (ops : ExternalFuns) (values : Slice ProverRw21FlatOutput.W)
    (bound : 32*values.length≤Usize.max)
    (canonical : ∀ x∈values.val,ProverRw21WideCarrier.canonical x) :
    ∃ result, @prover.encoded_slice _ (ProverRwP6BodyStore.selected ops) values=ok result ∧
      result.val.map ProverRw21ByteCarrier.decode=values.val.flatMap
        (fun x => ProverRw21ProtocolOutput.wide (ProverRw21WideCarrier.value x)) :=
  ⟨ProverRw21EncodedSlice.output values bound,source ops values bound,
    ProverRw21SequenceImage.image values.val canonical⟩

#print axioms flat
#print axioms source
#print axioms image
end R1Z.ProverRw21InstalledImage
