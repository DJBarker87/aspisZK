import BatchedWeightsPushLoopAllPrefixV11
import AspisR1BatchedUsizeFlushBridgePublic
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BatchedWeightsPushOuterNoFlushV3
open AspisR1BatchedWeightsExtraction
open AspisR1BatchedWeightsPushLoopAllPrefixV11
abbrev BW := batched_weights.BatchedWeights
abbrev Usize := UScalar UScalarTy.Usize
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31

/-- The actual outer `push` non-flush branch: generated `push_loop` runs first,
then the exact source mask test is false and the state is returned unchanged.
The terms counter is intentionally unchanged; caller owns its increment. -/
theorem push_nonflush_success
    (index : Usize) (initial : BW) (power : Q) (basis : M)
    (hindex : index.val < initial.raw.length)
    (hraw : ∀ k : Usize, ∀ hk : k.val < 4,
      cellAt initial index hindex k hk <
        2^34 + (initial.terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (ha : power.c0.a.val < AspisV8R17.RawReducer.P)
    (hb : power.c0.b.val < AspisV8R17.RawReducer.P)
    (hc : power.c1.a.val < AspisV8R17.RawReducer.P)
    (hd : power.c1.b.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hnoFlush : initial.terms.val % 4 ≠ 3) :
    ∃ mid : BW,
      batched_weights.BatchedWeights.push_loop
        ({ start := 0#usize, «end» := 4#usize } : Range)
        initial index basis
        (Array.make 4#usize [power.c0.a,power.c0.b,power.c1.a,power.c1.b]) = .ok mid ∧
      batched_weights.BatchedWeights.push initial index power basis = .ok mid ∧
      mid.terms = initial.terms := by
  obtain ⟨mid,hloop,hpost⟩ := push_loop_all_prefix index initial power basis
    hindex hraw ha hb hc hd hbasis
  have hmidTerms : mid.terms = initial.terms := hpost.1
  have hmask : ¬ (mid.terms &&& 3#usize = 3#usize) := by
    intro hm
    have hv := congrArg UScalar.val hm
    have htest : (UScalar.and mid.terms (3#usize)).val = 3 := by
      calc
        (UScalar.and mid.terms (3#usize)).val =
            mid.terms.val &&& (3#usize).val := UScalar.val_and _ _
        _ = 3 := by simpa using hv
    have hmod := (AspisR1BatchedUsizeFlushBridgePublic.source_usize_flush_test_iff
      mid.terms).1 htest
    rw [hmidTerms] at hmod
    exact hnoFlush hmod
  refine ⟨mid,hloop,?_,hmidTerms⟩
  simp [batched_weights.BatchedWeights.push, hloop, lift, bind_tc_ok, hmask]

#print axioms push_nonflush_success
end BatchedWeightsPushOuterNoFlushV3
