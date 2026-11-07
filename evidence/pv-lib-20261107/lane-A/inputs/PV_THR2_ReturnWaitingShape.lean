import PV_THR2_QuietTraceCertificate
set_option autoImplicit false
namespace PV_THR2_ReturnWaitingShape
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: a fresh
return instruction. Any running successor has no saved request, for every source store;
the read remains symbolic and a missing read remains its actual gap. -/
theorem source {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (site : Site) (place : Place)
    (rest : List PV_STX2_SliceSyntax.Node)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = .leaf (.ret site place) :: rest) :
    ∀ d, (PV_STX2_SliceMachine.step base ctl programs handler c w).status = .running d →
      d.frame.waiting = none := by
  simp only [PV_STX2_SliceMachine.step,done,waiting,remaining,
    PV_STX2_SliceMachine.native,PV_STX2_Native.step,PV_STX2_SliceMachine.adopt,Id.run,pure]
  cases value : PV_STX2_Store.read base c.store w c.frame.activation place with
  | none => simp only [value]; intro d h; cases h
  | some v =>
    simp only [value]
    cases parents : c.callers with
    | nil => intro d h; cases h
    | cons p ps =>
      intro d h
      cases h
      rfl
/-- Conditional on owner acceptance of amended translator. Hypotheses: fresh
return instruction. The uniform completion wrapper preserves the fresh saved-request shape. -/
theorem execution {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (c : Config) (w : W) (site : Site) (place : Place)
    (rest : List PV_STX2_SliceSyntax.Node)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = .leaf (.ret site place) :: rest) :
    ∀ d, (PV_THR2_Execution.step base ctl programs handler c w).status = .running d →
      d.frame.waiting = none := by
  have inactive : PV_THR2_Dynamic.active c = none := by
    simp only [PV_THR2_Dynamic.active,done,waiting,remaining]
  have old := source base ctl programs handler c w site place rest done waiting remaining
  have extra := source (PV_THR2_AggregateCompletion.carrier base) ctl programs handler c w site place rest done waiting remaining
  simp only [PV_THR2_Execution.step,inactive,PV_THR2_GapCompletion.step]
  generalize result : PV_STX2_SliceMachine.step base ctl programs handler c w = q at *
  cases status : q.status <;> simp only [status]
  · simpa only [status] using old
  · simpa only [status] using old
  · simpa only [status] using old
  · exact extra
#print axioms source
#print axioms execution
end PV_THR2_ReturnWaitingShape
