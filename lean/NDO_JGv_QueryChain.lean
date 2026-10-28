import NDO_JFz_TX2_AccumulationChain
import NDO_JGc_TX2_QueryDictionary
import NDO_JGv_QueryFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_QueryChain
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K
/-- A scalar invariant is transported along the actual successful sequence.
The prefix is obtained from the existing returning source, then identified by
Result determinism; no second selected accumulator is used. -/
theorem source {C : Type} (err : C) (geometry : Port3_NativeGeometryBody.Ops C)
    (seed : Port3_NativeQueryBody.Ops) (rhs : Nat → E) (power : Nat → K)
    (initialRhs : JFo_Prepared.accumulator.rhs=rhs 0)
    (initialPower : JFo_Prepared.accumulator.power=power 0)
    (step : ∀ n,n<12 → ∀ a b out after,
      a.weights=JFo_Prepared.accumulator.weights →
      a.rhs=rhs n → a.power=power n →
      JFz_TX2_ChainStep.transition seed n (a,b)=ok (out,after) →
      out.rhs=rhs (n+1) ∧ out.power=power (n+1))
    (n : Nat) (bound : n≤12) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (call : JFz_TX2_AccumulationChain.updates seed n=ok (a,b)) :
    a.rhs=rhs n ∧ a.power=power n := by
  induction n generalizing a b with
  | zero =>
    have same : (JFo_Prepared.accumulator,JFo_Pending.value)=(a,b) := Result.ok.inj call
    cases same
    exact ⟨initialRhs,initialPower⟩
  | succ n ih =>
    obtain ⟨previous,pending,previousCall,inv⟩ := JFz_TX2_AccumulationChain.source err geometry seed n (by omega)
    have scalar := ih (by omega) previous pending previousCall
    change (do
      let state ← JFz_TX2_AccumulationChain.updates seed n
      JFz_TX2_ChainStep.transition seed n state)=ok (a,b) at call
    rw [previousCall,bind_tc_ok] at call
    exact step n (by omega) previous pending a b inv.1 scalar.1 scalar.2 call
#print axioms source
end AspisR1.JGv_QueryChain
end
