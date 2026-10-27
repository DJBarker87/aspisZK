import R1Z.ProverRw21InstalledImage
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21FiniteImage
open Aeneas Aeneas.Std Result ProverRwFull ProverRw21WideCarrier
variable [ExternalTypes]

def input {n : Nat} (values : Fin n → E) (bound : 32*n≤Usize.max) : Slice W :=
  ⟨List.ofFn (fun i => encode (values i)),by rw [List.length_ofFn];omega⟩

theorem capacity {n : Nat} (values : Fin n → E) (bound : 32*n≤Usize.max) :
    32*(input values bound).length≤Usize.max := by
  change 32*(List.ofFn (fun i => encode (values i))).length≤Usize.max
  simpa only [List.length_ofFn] using bound

theorem source {n : Nat} (ops : ExternalFuns) (values : Fin n → E)
    (bound : 32*n≤Usize.max) :
    ∃ result, @prover.encoded_slice _ (ProverRwP6BodyStore.selected ops) (input values bound)=ok result ∧
      result.val=(ProverRw21ProtocolOutput.wides values).map ProverRw19MathematicalAssembly.byte := by
  refine ⟨ProverRw21EncodedSlice.output (input values bound) (capacity values bound),
    ProverRw21InstalledImage.source ops _ (capacity values bound),?_⟩
  change ProverRw21FlatSequence.bytes (List.ofFn (fun i => encode (values i)))=_
  have hin : List.ofFn (fun i => encode (values i))=(List.ofFn values).map encode := by
    rw [List.map_ofFn]
    rfl
  rw [hin,ProverRw21SequenceImage.encoded]
  congr 1
  unfold ProverRw21ProtocolOutput.wides
  rw [List.flatMap_def, List.map_ofFn]
  rfl

#print axioms input
#print axioms capacity
#print axioms source
end R1Z.ProverRw21FiniteImage
