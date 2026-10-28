import R1Z.ProverCommitFuelJoin22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RunJoinMap32
open R0Z R0Z.FsAbort

/-- Deterministic postprocessing preserves the EXACT coupling and bad event,
including the model's query stream. It never replaces a view by proof bytes. -/
def map {R M V W : Type} [Fintype R] [Fintype M]
    {runtime : R → V} {model : M → V}
    {old : Fin 8 → M → Prop} {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : ProverCommitFuelJoin22.RunJoin runtime model old queries) (f : V → W) :
    ProverCommitFuelJoin22.RunJoin (fun r => f (runtime r)) (fun m => f (model m)) old queries where
  cp := join.cp
  agreement := fun s good => congrArg f (join.agreement s good)
#print axioms map

/-- Complete view and observer decision on the same sample and failure event.
The decision consumes the entire view supplied as V. -/
def observer_pair {R M V D : Type} [Fintype R] [Fintype M]
    {runtime : R → V} {model : M → V}
    {old : Fin 8 → M → Prop} {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : ProverCommitFuelJoin22.RunJoin runtime model old queries) (decide : V → D) :
    ProverCommitFuelJoin22.RunJoin
      (fun r => (runtime r,decide (runtime r)))
      (fun m => (model m,decide (model m))) old queries :=
  map join (fun v => (v,decide v))
#print axioms observer_pair

theorem same_coupling {R M V D : Type} [Fintype R] [Fintype M]
    {runtime : R → V} {model : M → V}
    {old : Fin 8 → M → Prop} {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : ProverCommitFuelJoin22.RunJoin runtime model old queries) (decide : V → D) :
    (observer_pair join decide).cp=join.cp := rfl
#print axioms same_coupling
end R1Z.PV_RunJoin_RunJoinMap32
