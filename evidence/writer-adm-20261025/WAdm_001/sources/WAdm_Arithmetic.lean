import Tx1Q_Execution
import Tx1Q_Initial
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Arithmetic
open AspisR1Stage2 Port3_NativeQueryBody Tx1Q_Carriers

/-- Canonicality follows along the actual successful calls, without any
parser, semantic matching, selected-map, or model-state equality premise. -/
theorem calls (ops : Ops) (arithmetic : Port4C_QueryArithmetic.SessionABackends ops)
    (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
    (stop : Nat) (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n : Nat)
    (rho : Port3_FlushInstall.Canonical p.rho)
    (line : ∀ alpha values inverses value,
      ops.op16 alpha values inverses = ok value → Port4C_QueryArithmetic.CanonE value)
    (power : Port3_FlushInstall.Canonical a.power)
    (rhs : Port4C_QueryArithmetic.CanonE a.rhs)
    (actual : Port2_QueryLoop.Calls
      (fun a b => verifier.candidate.query_values ops proof p a g obs geo b)
      stop a b out bout n) :
    Port4C_QueryArithmetic.CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  induction actual with
  | done => exact ⟨rhs,power⟩
  | step active returned tail ih =>
    obtain ⟨o,_,_,_,_,cr,cp⟩ := Port4C_QueryArithmetic.query ops arithmetic
      proof p _ _ g obs geo _ _ power rho rhs line returned
    exact ih cp cr

#print axioms calls
end AspisR1.WAdm_Arithmetic
end
