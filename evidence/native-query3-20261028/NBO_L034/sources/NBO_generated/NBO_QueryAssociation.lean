import NBO_AccumulateAssociation
import Port4A_ReaderNormalize
set_option autoImplicit false
noncomputable section
namespace NBO_QueryAssociation
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev sourceOps (ops : Ops) := NBO_AccumulateAssociation.sourceOps ops
/-- Exact caller dictionary: decoder closure/from_fn and every callee use
are the actual emitted operations on the SAME carriers. No query result,
loop-result equation or independently chosen child output is a field. -/
def reference (ops : Ops) : QueryOps :=
 {opening:=(sourceOps ops).op11,dots:=(sourceOps ops).op20,
  inverse:=(sourceOps ops).op18,circle:=(sourceOps ops).op17,
  values:=fun q=>(sourceOps ops).op0 4#usize
    (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (sourceOps ops)) q,
  ne:=core.cmp.PartialEq.ne.trait_default (sourceOps ops).widePartialEq,
  line:=(sourceOps ops).op16,mulM:=(sourceOps ops).op7,doubleM:=(sourceOps ops).op8,
  oneM:=(sourceOps ops).op5,subM:=(sourceOps ops).op6,
  mark:=(sourceOps ops).op19,trace:=(sourceOps ops).op15}
/-- Complete emitted query_values association to one concrete checked
reference instance. Every Result path is retained; arithmetic normalization
uses only the reached counters/geometry order, not a successful query output. -/
theorem source (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (size : a.weights.val.length=64)
 (raw : b.raw.val.length=64) (active : a.next.val<10)
 (sync : b.terms=a.next) (order : geometry.start.val≤a.next.val) :
 verifier.candidate.query_values (sourceOps ops) proof p a g obs geometry b =
 AspisR1Stage2.verifier.candidate.queryWithOps
   (NBO_AccumulateAssociation.reference ops) (reference ops) proof p a g obs geometry b := by
 have mul4 := NBF_BasisInstall.checked_mul 4#usize a.next
   (by change 4*a.next.val≤4096;omega)
 have mul2 := NBF_BasisInstall.checked_mul 2#usize a.next
   (by change 2*a.next.val≤4096;omega)
 have val4 := Port3_Wrapping.wrap_mul_value 4#usize a.next
   (by change 4*a.next.val≤4096;omega)
 have val2 := Port3_Wrapping.wrap_mul_value 2#usize a.next
   (by change 2*a.next.val≤4096;omega)
 have add41 := Port3_Wrapping.checked_add (Usize.wrapping_mul 4#usize a.next) 1#usize
   (by rw [val4];change 4*a.next.val+1≤4096;omega)
 have add42 := Port3_Wrapping.checked_add (Usize.wrapping_mul 4#usize a.next) 2#usize
   (by rw [val4];change 4*a.next.val+2≤4096;omega)
 have add43 := Port3_Wrapping.checked_add (Usize.wrapping_mul 4#usize a.next) 3#usize
   (by rw [val4];change 4*a.next.val+3≤4096;omega)
 have add21 := Port3_Wrapping.checked_add (Usize.wrapping_mul 2#usize a.next) 1#usize
   (by rw [val2];change 2*a.next.val+1≤4096;omega)
 have offset := Port4A_ReaderNormalize.checked_sub a.next geometry.start order
 have accumulation : ∀ node value,
   verifier.accumulate_batched_with_node (sourceOps ops) p a node value b =
   AspisR1Stage2.verifier.accumulateWithOps (NBO_AccumulateAssociation.reference ops)
     p a node value b := fun node value=>
   NBO_AccumulateAssociation.source ops p a node value b size raw active sync
 unfold verifier.candidate.query_values AspisR1Stage2.verifier.candidate.queryWithOps reference
 simp only [mul4,mul2,add41,add42,add43,add21,offset,lift,bind_tc_ok,accumulation]
#print axioms source
end NBO_QueryAssociation
end
