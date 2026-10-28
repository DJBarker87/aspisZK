import R1Z.PV_Src_PortSumTrace

/-! The generated iterator carries extra default-method fields. Its next
operation is the same mapped next; finite traces transport through that exact
projection, without equating unrelated method dictionaries. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortSumAdapter
open Aeneas Aeneas.Std Result BuilderStdModels

abbrev iterator :=
  BuilderForestStdPort.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    (core.iter.traits.iterator.IteratorSliceIter U32) PV_Src_PortSumTrace.castClosure

theorem trace_transport
    (i : core.iter.adapters.map.Map (core.slice.iter.Iter U32) Unit) (xs : List U64)
    (ht : FiniteTrace (mappedIterator (core.iter.traits.iterator.IteratorSliceIter U32)
      PV_Src_PortSumTrace.castClosure) i xs) : FiniteTrace iterator i xs := by
  induction ht with
  | done it it' hn => exact .done _ it' hn
  | step it it' x xs hn tail ih => exact .step _ it' x xs hn ih

theorem cast_trace (s : Slice U32) (i : Nat) :
    FiniteTrace iterator ⟨⟨s,i⟩,()⟩ ((s.val.drop i).map (UScalar.cast .U64)) :=
  trace_transport _ _ (PV_Src_PortSumTrace.cast_trace s i)

theorem sum (s : Slice U32) (i : Nat) (acc : U64) :
    BuilderForestStd.sumLoop iterator ⟨⟨s,i⟩,()⟩ acc =
      PV_Src_PortSumTrace.fold ((s.val.drop i).map (UScalar.cast .U64)) acc :=
  PV_Src_PortSumTrace.trace _ _ _ (cast_trace s i) acc

#print axioms trace_transport
#print axioms cast_trace
#print axioms sum
end R1Z.PV_Src_PortSumAdapter
