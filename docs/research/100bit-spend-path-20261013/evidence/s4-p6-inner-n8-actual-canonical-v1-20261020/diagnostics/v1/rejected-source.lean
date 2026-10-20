import S4FromFnP6InnerN8ArrayFieldV1
import ExtractedCurrentReducer

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false
namespace AspisR1FromFnP6Generated

def fourDotsOpsWithActualReducer (ops : FourDotsOps) : FourDotsOps :=
  { ops with m31ReduceU64 := AspisR1Qm31ArithmeticProbe.field.reduce_u64 }

private theorem actual_reducer_success_canonical (w : U64) (z : U32)
    (h : AspisR1Qm31ArithmeticProbe.field.reduce_u64 w = .ok z) :
    z.val < AspisR1.ExtractedCurrentReducer.P := by
  obtain ⟨out,hout,_hmod,hbound⟩ :=
    AspisR1.ExtractedCurrentReducer.current_reduce_mod w
  have heq : out = z := Result.ok.inj (hout.symm.trans h)
  simpa only [heq] using hbound

/-- The actual reducer is canonical for every UInt64 input. The seven-batch
bound is needed for the earlier additions, not as an extra premise here. -/
theorem generatedInnerN8_actualReducer_success_canonical
    (ops : FourDotsOps)
    (limbs : fast_dots.four_dots.closure.closure)
    (values : Aeneas.Std.Array U32 8#usize)
    (h : (fourDotsOpsWithP6ArrayFromFnN8
        (fourDotsOpsWithActualReducer ops)).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN8 (fourDotsOpsWithActualReducer ops)))
      limbs = .ok values) :
    ∀ value ∈ values.val, value.val < AspisR1.ExtractedCurrentReducer.P := by
  obtain ⟨m0,m1,m2,m3,m4,m5,m6,m7,w0,w1,w2,w3,w4,w5,w6,w7,
      hvalues,_hi0,hr0,_hi1,hr1,_hi2,hr2,_hi3,hr3,
      _hi4,hr4,_hi5,hr5,_hi6,hr6,_hi7,hr7⟩ :=
    generatedInnerN8ArrayField_success_values_match_fixedV6
      (fourDotsOpsWithActualReducer ops) limbs values h
  have hc0 := actual_reducer_success_canonical w0 m0 hr0
  have hc1 := actual_reducer_success_canonical w1 m1 hr1
  have hc2 := actual_reducer_success_canonical w2 m2 hr2
  have hc3 := actual_reducer_success_canonical w3 m3 hr3
  have hc4 := actual_reducer_success_canonical w4 m4 hr4
  have hc5 := actual_reducer_success_canonical w5 m5 hr5
  have hc6 := actual_reducer_success_canonical w6 m6 hr6
  have hc7 := actual_reducer_success_canonical w7 m7 hr7
  intro value hv
  rw [hvalues] at hv
  simp only [List.mem_cons,List.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

#print axioms generatedInnerN8_actualReducer_success_canonical
end AspisR1FromFnP6Generated
