import Port3_QueryStage
import NEB_PureFrame
set_option autoImplicit false
namespace NEO_ObserverPort
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- The deployed cohort port at every Phase, including arbitrary Query indices.
Native no-effect specialization is the adopted ruling z(1), separately pinned;
this statement makes no assertion about a function-pointer-valued Kani run. -/
theorem mark (ops : Port3_NativeQueryBody.Ops) (phase : verifier.Phase) :
    (Port3_QueryStage.release ops).op19 none phase = ok () :=
  Port3_QueryStage.mark_none phase

/-- No successful continuation result is postulated; any Result, including
panic/error/divergence, passes through the exact source port unchanged. -/
theorem continuation {A : Type} (ops : Port3_NativeQueryBody.Ops)
    (phase : verifier.Phase) (next : Result A) :
    (do let _ ← (Port3_QueryStage.release ops).op19 none phase; next) = next := by
  rw [mark]
  rfl

/-- Pure frame on that same installed mark call, for an arbitrary state and
ordered-effect type. The native frame is supplied by ruling z(1), not inferred
from this lift for an unspecified native implementation. -/
theorem frame {S Event : Type} (state : S) (ops : Port3_NativeQueryBody.Ops)
    (phase : verifier.Phase) :
    NEB_PureFrame.run (Event:=Event) state
      ((Port3_QueryStage.release ops).op19 none phase) = ok ((),state,[]) := by
  exact NEB_PureFrame.successful state _ _ (mark ops phase)

#print axioms mark
#print axioms continuation
#print axioms frame
end NEO_ObserverPort
