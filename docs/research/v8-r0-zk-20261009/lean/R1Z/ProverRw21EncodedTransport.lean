import R1Z.ProverRw21EncodedImage
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21EncodedTransport
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem step (left right : ExternalFuns) (same : left.op51=right.op51) :
    @prover.encoded_slice_loop.body _ left = @prover.encoded_slice_loop.body _ right := by
  funext values out i
  simp only [prover.encoded_slice_loop.body,aspis_core.field.wide_exact.WideExact.to_le_bytes,same]

theorem loop (left right : ExternalFuns) (same : left.op51=right.op51) :
    @prover.encoded_slice_loop _ left = @prover.encoded_slice_loop _ right := by
  funext values out i
  unfold prover.encoded_slice_loop
  rw [step left right same]

theorem slice (left right : ExternalFuns) (same : left.op51=right.op51) :
    @prover.encoded_slice _ left = @prover.encoded_slice _ right := by
  funext values
  simp only [prover.encoded_slice,loop left right same]

theorem source (ops : ExternalFuns)
    (flat : ops.op51=ProverRwP6FlatSource.wide_bytes_flat)
    (values : Slice ProverRw21FlatOutput.W) (bound : 32*values.length≤Usize.max) :
    @prover.encoded_slice _ ops values=ok (ProverRw21EncodedSlice.output values bound) := by
  rw [slice ops (ProverRw21EncodedStep.selected ops) flat]
  exact ProverRw21EncodedSlice.source ops values bound

#print axioms step
#print axioms loop
#print axioms slice
#print axioms source
end R1Z.ProverRw21EncodedTransport
