import XRz_PushCanonical
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
noncomputable section
namespace XRz_PushReach
open S7Kani2OwnedRowRefinement S7Kani3CallerTrace
/-- Exact carrier injectivity: no pending state can be silently reselected. -/
theorem injective : Function.Injective XRu_PushTransport.bw := by
 intro a b h
 cases a
 cases b
 cases h
 rfl
/-- The emitted push produces the SAME source trace extension, rather than
requiring an independent successful owned push or a selected output. -/
theorem source (old : S8OwnedP6Finish.Weights) (b : verifier.BatchedWeights) (sum : Sum)
 (history : PushTrace old (XRu_PushTransport.bw b) sum)
 (i : Usize) (q : aspis_core.field.QM31) (m : U32) (x : Fin 4 → U64)
 (bound : i.val<b.raw.length) (get : b.raw.val[i.val]?=some (makeRow x))
 (canonical : ∀ k, (powerLimb (XRu_PushTransport.power q) k).val<2^31-1)
 (basis : m.val<2^31-1) (phase : ∀ k, S7Kani3PhaseInvariant.Phase b.terms.val (x k).val) :
 ∃ after : verifier.BatchedWeights,
 verifier.BatchedWeights.push b i q m=ok after ∧
 PushTrace old (XRu_PushTransport.bw after)
  (Function.update sum i.val (fun k => sum i.val k+(powerLimb (XRu_PushTransport.power q) k).val*m.val)) := by
 obtain ⟨y,run,_,_⟩ := S7Kani3CallerStep.push_caller_invariant (XRu_PushTransport.bw b) old sum
  (reached_invariant old _ sum history) i (XRu_PushTransport.power q) m x bound get canonical basis phase
 let after : verifier.BatchedWeights := ⟨b.raw.set i (makeRow y),b.terms⟩
 have same := XRz_PushCanonical.source b i q m x bound get canonical basis phase
 have mapped : XRo_Join_Carriers.mapR XRu_PushTransport.bw (verifier.BatchedWeights.push b i q m)=
  XRo_Join_Carriers.mapR XRu_PushTransport.bw (ok after) := same.trans run
 have emitted := XRo_Join_ResultTransport.map_injective XRu_PushTransport.bw injective _ _ mapped
 refine ⟨after,emitted,?_⟩
 exact PushTrace.push history i (XRu_PushTransport.power q) m x bound get canonical basis phase run
#print axioms injective
#print axioms source
end XRz_PushReach
