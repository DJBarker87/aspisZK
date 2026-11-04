import NEW_InverseAssociation
import NEO_InverseLog
import NEB_PureFrame
set_option autoImplicit false
namespace NEW_InverseComplete
open Aeneas Aeneas.Std Result AspisR1

/-- Actual-body extraction identifies the full independent reference, including rejection. -/
theorem reference (x : U32) : NEW_InverseActual.aspis_core.field.M31.inv x =
    NEO_TailRef.inverse NEO_TailReference.inverseOps x :=
  (NEW_InverseAssociation.emitted x).trans (NEO_TailReference.inverse x).symm

/-- Entire Result/state/semantic-effects lift on the same model state.
The runtime's panic interpretation is retained; no empty native panic-I/O claim. -/
theorem result_state_effects {S Event : Type} (state : S) (x : U32) :
    NEB_PureFrame.run (Event:=Event) state (NEW_InverseActual.aspis_core.field.M31.inv x) =
      NEB_PureFrame.run (Event:=Event) state (Port4C_InverseExecution.inverse_owned x) := by
  rw [NEW_InverseAssociation.cohort]

/-- Reuse the already proved legal DAG. The returned word is now tied to the
ACTUAL frozen extraction, rather than only to the earlier logged clone. -/
theorem nonzero_calls (x : U32) (nonzero : x != 0#u32) :
 ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
 let calls := NEO_InverseLog.chain x m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out
 calls.length=17 ∧ (∀ call∈calls,NEO_InverseLog.legal call) ∧
 NEW_InverseActual.aspis_core.field.M31.inv x=ok out ∧ out.val<2147483647 := by
 obtain ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,count,legal,run,canonical⟩ :=
   NEO_InverseLog.nonzero x nonzero
 exact ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,count,legal,
   (reference x).trans run,canonical⟩

#print axioms reference
#print axioms result_state_effects
#print axioms nonzero_calls
end NEW_InverseComplete
