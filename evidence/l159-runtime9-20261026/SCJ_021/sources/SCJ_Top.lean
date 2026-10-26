import SCI_Recovery
import SCJ_Composition
import SCJ_EventTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Top
/-- A limit on dropping the binding while retaining an unrestricted Runtime
quantifier. This is not a counterexample jointly instantiating all Rc8
hypotheses, nor a counterexample to a theorem on the actual SCE runtime. -/
theorem unrestricted_runtime_obstruction :
    ¬ (∀ runtime : F3T_Runtime.Runtime,
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total 0) := by
  intro all
  exact SCI_Recovery.ObserverBoundary.not_zero_query_conclusion
    (all SCI_Recovery.ObserverBoundary.runtime)

#print axioms unrestricted_runtime_obstruction
end AspisR1.SCJ_Top
end
