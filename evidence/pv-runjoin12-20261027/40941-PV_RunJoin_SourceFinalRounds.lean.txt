import R1Z.PV_RunJoin_SourceRoundFold
import R1Z.PV_RunJoin_SourceFinalStep
/-! Proof draft reused read-only from srcid d597d31545. This new module is checked independently; no upstream draft is assumed compiled. -/

/-! Finite source iteration agrees with symbolic copy rounds, preserving the
entire trace-callback Result and threaded callback state. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceFinalRounds
open Aeneas Aeneas.Std Result BuilderStdModels
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_SourceRoundFold

abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter (Array U32 16#usize))
def iterator : core.iter.traits.iterator.Iterator Iter (Usize × State) where
  next := core.iter.adapters.enumerate.IteratorEnumerate.next
    (core.iter.traits.iterator.IteratorSliceIter (Array U32 16#usize))

theorem source {F : Type}
    (callback : core.ops.function.FnMut F poseidon2.Poseidon2RoundTransition Unit)
    (iter : Iter) (xs : List (Usize × State)) (ht : FiniteTrace iterator iter xs)
    (s input : State) (trace : F) (round : U8) (hs : Canonical s)
    (hc : ∀ p ∈ xs, Canonical p.2) :
    poseidon2.permute_optimized_with_trace_loop2
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) callback iter s trace round input =
      (do
        let p ← fullSteps callback (fun i => poseidon2.Poseidon2RoundKind.ExternalFinal (UScalar.cast .U8 i))
          xs s trace round input
        ok (p.1,p.2.1)) := by
  letI : ExternalLinear := PV_Src_ExternalReference.dictionary
  induction ht generalizing s input trace round with
  | done it it' hn =>
    simp only [iterator] at hn
    rw [poseidon2.permute_optimized_with_trace_loop2,hn]
    rfl
  | step it it' p xs hn tail ih =>
    simp only [iterator] at hn
    rcases p with ⟨index,c⟩
    have hconst : Canonical c := hc (index,c) (by simp)
    have htail : ∀ p ∈ xs, Canonical p.2 := fun p hp => hc p (by simp [hp])
    rw [PV_RunJoin_SourceFinalStep.source callback it it' s input trace round index c hn hs hconst]
    obtain ⟨out,ho,hcan⟩ := full_total s c
    simp only [fullSteps,ho,bind_tc_ok,bind_assoc_eq]
    congr 1
    funext p
    exact ih out out p.2 (U8.wrapping_add round 1#u8) hcan htail

#print axioms source
end R1Z.PV_RunJoin_SourceFinalRounds
