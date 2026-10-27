import R1Z.ProverRw21EncodedLoop
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21EncodedSlice
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw21EncodedStep
variable [ExternalTypes]

def output (values : Slice W) (bound : 32*values.length≤Usize.max) : alloc.vec.Vec U8 :=
  ⟨ProverRw21FlatSequence.bytes values.val,by
    simpa only [ProverRw21FlatSequence.length] using bound⟩

/-- Exact bytes for the retained source loop with its selected P6 serializer.
The size premise is the actual usize allocation/append capacity, not a claim
that the deployed protocol produces a particular sequence of field values. -/
theorem source (ops : ExternalFuns) (values : Slice W)
    (bound : 32*values.length≤Usize.max) :
    @prover.encoded_slice _ (selected ops) values=ok (output values bound) := by
  unfold prover.encoded_slice
  simp only [lift,bind_tc_ok]
  rw [ProverRw21EncodedLoop.run ops values values.length _ 0#usize (by rfl) (by
    change 0+32*(values.length-0)≤Usize.max
    simpa only [Nat.zero_add,Nat.sub_zero] using bound)]
  rfl

#print axioms output
#print axioms source
end R1Z.ProverRw21EncodedSlice
