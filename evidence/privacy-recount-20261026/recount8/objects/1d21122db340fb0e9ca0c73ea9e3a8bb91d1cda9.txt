import R1Z.PV_RunJoin_EnumerateTrace
import R1Z.PV_RunJoin_SourceInitialRounds
import R1Z.PV_RunJoin_SourceInternalRounds

/-! Finite traces for the actual slice/array enumeration adapters. Data remain
symbolic; only their lengths and the small enumeration counter are bounded. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RoundTableTrace
open Aeneas Aeneas.Std Result BuilderStdModels
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep

def sliceIter {n : Usize} (a : Array State n) : PV_RunJoin_SourceInitialRounds.Iter :=
  ⟨⟨Array.to_slice a,0⟩,0#usize⟩

abbrev arrayIterator :=
  core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator U32 14#usize

def arrayIter (a : Array U32 14#usize) : PV_RunJoin_SourceInternalRounds.Iter :=
  ⟨a.val,0#usize⟩

theorem array_base (xs : List U32) : FiniteTrace arrayIterator xs xs := by
  induction xs with
  | nil => exact .done [] [] rfl
  | cons x xs ih => exact .step (x::xs) xs x xs rfl ih

theorem slice_trace {n : Usize} (a : Array State n) (hn : n.val ≤ 20) :
    FiniteTrace PV_RunJoin_SourceInitialRounds.iterator (sliceIter a)
      (PV_RunJoin_EnumerateTrace.labels 0#usize a.val) := by
  change FiniteTrace
    (PV_RunJoin_EnumerateTrace.enumerated
      (core.iter.traits.iterator.IteratorSliceIter State)) _ _
  apply PV_RunJoin_EnumerateTrace.trace
  · simpa only [List.drop_zero,Array.val_to_slice] using BuilderSliceCollect.slice_trace (Array.to_slice a) 0
  · change 0 + a.val.length ≤ 20
    rw [a.property]
    omega

theorem array_trace (a : Array U32 14#usize) :
    FiniteTrace PV_RunJoin_SourceInternalRounds.iterator (arrayIter a)
      (PV_RunJoin_EnumerateTrace.labels 0#usize a.val) := by
  change FiniteTrace (PV_RunJoin_EnumerateTrace.enumerated arrayIterator) _ _
  apply PV_RunJoin_EnumerateTrace.trace
  · exact array_base a.val
  · change 0 + a.val.length ≤ 20
    rw [a.property]
    decide

theorem slice_prepare {n : Usize} (a : Array State n) :
    (do
      let s ← lift (Array.to_slice a)
      let i ← core.slice.Slice.iter s
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter State) i) = ok (sliceIter a) := rfl

theorem array_prepare (a : Array U32 14#usize) :
    (do
      let i ← Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter a
      core.iter.traits.iterator.Iterator.enumerate.trait_default arrayIterator i) =
      ok (arrayIter a) := rfl

#print axioms array_base
#print axioms slice_trace
#print axioms array_trace
#print axioms slice_prepare
#print axioms array_prepare
end R1Z.PV_RunJoin_RoundTableTrace
