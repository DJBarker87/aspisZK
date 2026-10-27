import RPu_FJa_LocalWeightStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_LocalWeightFold
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FJa_PoseidonOrigins (Selectors)
abbrev Callback := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
def model (s : Selectors) (indices : List Usize) (acc : K) : K :=
  (indices.map (fun i=>FIv_NativeArray.value s.local i.val)).foldl (·+·) acc
/-- Symbolic value of the ORIGINAL array-iterator fold for arbitrary visited
indices; no concrete numerical recurrence reduction. -/
theorem value (N : Usize) (indices : List Usize) (s : Selectors) (acc out : NQ)
    (hs : FIw_ArrayValue.canonical s.local) (hc : Canon acc)
    (run : core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold
      (N:=N) Callback indices acc s=ok out) :
    Canon out ∧ decode out=model s indices (decode acc) := by
  induction indices generalizing acc with
  | nil =>
    have same : acc=out := Result.ok.inj run
    subst out
    exact ⟨hc,rfl⟩
  | cons index rest ih =>
    rw [core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.fold] at run
    obtain ⟨⟨next,last⟩,hstep,run⟩ := FIv_Map.bind_success _ _ _ run
    have step := FJa_LocalWeightStep.value s last acc next index hs hc hstep
    have eq := step.2.2
    subst last
    have tail := ih next step.1 run
    refine ⟨tail.1,?_⟩
    rw [tail.2,step.2.1]
    rfl
#print axioms value
end AspisR1.FJa_LocalWeightFold
end
