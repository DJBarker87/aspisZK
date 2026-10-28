import R1Z.PV_RunJoin_WideLoop38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WideComplete38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WideStep38 PV_RunJoin_WideLoop38
variable [ExternalTypes]

/-- Entire emitted wide-cell serializer, on any size that fits the backend
vector. All eight source limbs are retained for each cell. Capacity is a value
model bound; no native allocator or failure-world claim is inferred. -/
theorem encode (ops : ExternalFuns) (size : Usize) (f : Nat → W)
    (room : 32*size.val≤Usize.max) :
    ∃ bytes,
      @prover.encoded_slice _ (ProverRwP6BodyCandidate.selected ops) (input size f)=.ok bytes ∧
      bytes.val=payload f 0 size.val ∧ bytes.val.length=32*size.val := by
  obtain ⟨bytes,hbytes,hval⟩ := complete ops size f size.val 0#usize
    (alloc.vec.Vec.with_capacity U8 (Usize.wrapping_mul 32#usize size))
    (by change 0+size.val=size.val;omega) (by change 0+32*size.val≤Usize.max;omega)
  refine ⟨bytes,?_,?_,?_⟩
  · unfold prover.encoded_slice
    rw [input_size]
    simp only [lift,bind_tc_ok]
    exact hbytes
  · simpa only [alloc.vec.Vec.with_capacity,List.nil_append,show (0#usize).val=0 from rfl] using hval
  · rw [hval]
    change ([] ++ payload f 0 size.val).length=32*size.val
    rw [List.nil_append,payload_length]

#print axioms encode
end R1Z.PV_RunJoin_WideComplete38
