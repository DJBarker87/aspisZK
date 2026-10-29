import PV_RJ4IDB_DiagAdapter
import PV_RJ4IDB_NativeFactor
set_option autoImplicit false
namespace PV_RJ4IDB
variable {S A : Type}
/-- Visible final-state channels are an explicit input from L1/diag. They are
retained even after abort/divergence; the private state itself is not declared
public. Earlier visible state changes must already occur in x.events. -/
def diagWithState (expose : S → List (Bytes × Bytes))
 (x : PV_DIAG3.Execution S A) : Trace A :=
 ⟨x.events.map Event.diagnostic3 ++ (expose x.state).map (fun p => .retained p.1 p.2),
 diagTerminal x.exit⟩

theorem diag_with_state_order (expose : S → List (Bytes × Bytes))
 (x : PV_DIAG3.Execution S A) :
 (decoder (diagWithState expose x)).ordered =
 x.events.map Event.diagnostic3 ++ (expose x.state).map (fun p => .retained p.1 p.2) := rfl

theorem final_state_abort (expose : S → List (Bytes × Bytes))
 (es : List PV_DIAG3.Event) (s : S) (c : PV_DIAG3.Crash) :
 diagWithState expose (⟨es,s,.abort c⟩ : PV_DIAG3.Execution S A) =
 ⟨es.map Event.diagnostic3 ++ (expose s).map (fun p => .retained p.1 p.2),.abort c⟩ := rfl

theorem final_state_divergence (expose : S → List (Bytes × Bytes))
 (es : List PV_DIAG3.Event) (s : S) :
 diagWithState expose (⟨es,s,.diverge⟩ : PV_DIAG3.Execution S A) =
 ⟨es.map Event.diagnostic3 ++ (expose s).map (fun p => .retained p.1 p.2),.diverge⟩ := rfl
#print axioms diag_with_state_order
#print axioms final_state_abort
#print axioms final_state_divergence
end PV_RJ4IDB
