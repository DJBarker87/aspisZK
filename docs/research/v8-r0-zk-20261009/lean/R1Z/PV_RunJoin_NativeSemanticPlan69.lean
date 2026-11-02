import R1Z.PV_RunJoin_NativeSemanticSuff69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSemanticPlan69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63 PV_RunJoin_Sequential64
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (self : @host_semantic.SemanticOracle (types base)) (point : Array Q 10#usize)
    (claims : Array (Array Q 29#usize) 3#usize)
    (terminal : Q)
    (ht : letI : ExternalTypes := types base
      @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        (types base) ops self.«public» claims point self.challenges=ok (.Ok terminal)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    Success runtime (.terminal self.«public» claims point self.challenges
      (fun status => .step (PV_RunJoin_SemanticReached69.tail self point claims status) Plan.done)) world := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have ht' : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      self.«public» claims point self.challenges=ok (.Ok terminal) := by
    change @ExternalFuns.op227 (types base) (opsNative base heap box ops runtime world) _ _ _ _=_
    rw [PV_RunJoin_NativeFrames63.op227]
    exact ht
  obtain ⟨out,ho⟩ := PV_RunJoin_NativeSemanticSuff69.tail base heap box ops runtime world self point claims terminal
  exact Success.terminal self.«public» claims point self.challenges _ world terminal ht'
    (Success.step _ Plan.done world (.Ok out) ho (Success.done _ world))

#print axioms complete
end R1Z.PV_RunJoin_NativeSemanticPlan69
