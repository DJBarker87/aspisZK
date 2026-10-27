import R1Z.BuilderForestAdmissionPort
import R1Z.BuilderStdCollect
import R1Z.BuilderSliceCollect

/-! The actual checked iterator sum equals a finite source-order fold.
The complete Result is retained, including checked-add failure. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortSumTrace
open Aeneas Aeneas.Std Result BuilderStdModels
variable {I : Type}

def fold : List U64 → U64 → Result U64
  | [], acc => ok acc
  | x::xs, acc => do
    let next ← acc + x
    fold xs next

theorem trace (it : core.iter.traits.iterator.Iterator I U64)
    (i : I) (xs : List U64) (ht : FiniteTrace it i xs) (acc : U64) :
    BuilderForestStd.sumLoop it i acc = fold xs acc := by
  induction ht generalizing acc with
  | done i i' h =>
    rw [BuilderForestStd.sumLoop,h]
    rfl
  | step i i' x xs h tail ih =>
    rw [BuilderForestStd.sumLoop,h]
    simp only [bind_tc_ok,fold]
    simp only [ih]

abbrev castClosure := BuilderForestAdmissionPort.poseidon2.internal_linear_lazy.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31U64

theorem cast_trace (s : Slice U32) (i : Nat) :
    FiniteTrace (mappedIterator (core.iter.traits.iterator.IteratorSliceIter U32) castClosure)
      ⟨⟨s,i⟩,()⟩ ((s.val.drop i).map (UScalar.cast .U64)) :=
  mapped_trace _ _ _ (by intro c x; rfl) _ _ (BuilderSliceCollect.slice_trace s i) ()

theorem cast_sum (s : Slice U32) (i : Nat) (acc : U64) :
    BuilderForestStd.sumLoop
      (mappedIterator (core.iter.traits.iterator.IteratorSliceIter U32) castClosure)
      ⟨⟨s,i⟩,()⟩ acc = fold ((s.val.drop i).map (UScalar.cast .U64)) acc :=
  trace _ _ _ (cast_trace s i) acc

#print axioms trace
#print axioms cast_trace
#print axioms cast_sum
end R1Z.PV_Src_PortSumTrace
