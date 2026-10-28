import R1Z.PV_RunJoin_PolyLoop38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PolyComplete38
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38
variable [ExternalTypes]

/-- All 28 normalized field coefficients, in ascending coefficient order.
No oracle, canonicality, allocator-success or desired byte equality is assumed.
This is the current emitted Aeneas Result law; native allocation/copy effects
and association to the security-model polynomial are separate obligations. -/
theorem encode (ops : ExternalFuns) (p : Nat → Q) :
    ∃ bytes,
      @host_sumcheck.encode_polynomial _ (ProverRwP6BodyCandidate.selected ops)
        (ProverCommitArray49.array 28#usize p) = .ok bytes ∧
      bytes.val = payload p 0 28 ∧ bytes.val.length=896 := by
  obtain ⟨bytes,hbytes,hval⟩ := complete ops p 28 0#usize
    (alloc.vec.Vec.with_capacity U8 896#usize) rfl (by
      change 0+32*28≤Usize.max
      scalar_tac)
  refine ⟨bytes,hbytes,?_,?_⟩
  · simpa only [alloc.vec.Vec.with_capacity,List.nil_append,show (0#usize).val=0 from rfl] using hval
  · rw [hval]
    change ([] ++ payload p 0 28).length=896
    rw [List.nil_append,payload_length]

#print axioms encode
end R1Z.PV_RunJoin_PolyComplete38
