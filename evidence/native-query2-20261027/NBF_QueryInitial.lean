import NBF_QueryInvariant
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_QueryInitial
open AspisR1 AspisR1Stage2
/-- SAME initialized accumulator/pending source results establish the entire
query invariant. No initial row-phase or canonical-power premise is added. -/
theorem good (base : VTop_Stages.Ops) (reserved : Bool)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b)) :
 a.next=0#usize ∧ NBF_QueryInvariant.Good a b := by
 obtain ⟨reservedTrue,weights,rhs,power,next⟩ := Port3_Initial.accepted_fields base reserved a initial
 have size : a.weights.val.length=64 := by rw [weights,List.length_replicate]
 obtain ⟨terms,phase⟩ := NBF_FirstRows.constructor_progress reserved a.weights.deref b size pending
 refine ⟨next,size,terms.trans next.symm,?_,?_⟩
 · simpa only [next,show (0#usize).val=0 from rfl] using phase
 · rw [power]
   intro k
   fin_cases k <;> decide
#print axioms good
end NBF_QueryInitial
