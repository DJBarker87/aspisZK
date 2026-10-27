import WAdm_Domain
import WAdm_RunArithmetic
import WAdm_RunControl
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_RunDomain
open Tx1Q_Carriers

/-- The SAME run supplies every bounded writer value guard. Runtime/physical
carrier interpretation is deliberately not asserted by this value theorem. -/
theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : WAdm_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : WAdm_Domain.SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (proofLength : proof.val.length = 57607) (publicLength : pub.val.length = 1880) :
    WAdm_Domain.Admitted (prepared run.p)
      (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) proof pub := by
  have fields := owner.accepted D hash semantic proof run.zero run.p run.scratch run.prepare_call
  have mutable := WAdm_RunArithmetic.on_run installed reserved query geo D hash semantic pub proof split saved
    run ports fields.rho
  have control := WAdm_RunControl.fields installed reserved query geo D hash semantic pub proof split saved run
  refine ⟨fields.variant,?_,control.2.2.1,fields.gamma,fields.kappa,?_,fields.claim,
    mutable.1,proofLength,publicLength⟩
  · simpa only [accumulator,vec,List.length_map] using control.2.2.2.1
  · intro x member
    obtain ⟨i,hi,hx⟩ := List.getElem_of_mem member
    have bound : i < 2 := by
      rw [(prepared run.p).alpha.property] at hi
      exact hi
    have h := fields.alpha ⟨i,bound⟩
    rw [hx] at h
    exact h

#print axioms on_run
end AspisR1.WAdm_RunDomain
end
