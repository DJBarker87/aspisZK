import NNQ_Sim
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result S2W_Trace S2W_Outer

theorem sim_mapError {A : Type}
    (r : core.result.Result A AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    Sim (mapError traceEffects.op44 r) (mapError traceEffects.op44 r) := by
  cases r with
  | Ok x => exact sim_pure _
  | Err e => exact sim_bind (sim_perform (.same _ (by simp [NotDigest, S2W_Trace.operationId]))) (fun _ => sim_pure _)

theorem first_decoded_sim (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) :
    Sim (S2W_Outer.first_decoded {S with op43 := o} traceEffects semantic pub proof split)
      (S2W_Outer.first_decoded S traceEffects semantic pub proof split) := by
  unfold S2W_Outer.first_decoded
  simp only [AdapterRw.observer]
  apply sim_bind (sim_lift _)
  intro obs
  apply sim_bind
  · apply sim_perform
    apply CallSim.op10
    rfl
  · intro r
    exact sim_mapError r
#print axioms sim_mapError
#print axioms first_decoded_sim
end AspisR1.NNQ_HostDigest
end
