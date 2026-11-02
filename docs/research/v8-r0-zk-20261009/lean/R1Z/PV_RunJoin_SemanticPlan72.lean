import R1Z.PV_RunJoin_SemanticSuff72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticPlan72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63 PV_RunJoin_Sequential64
abbrev Q := aspis_core.field.QM31

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (self : @host_semantic.SemanticOracle (types base)) (point : Array Q 10#usize)
    (rows : letI : ExternalTypes := types base
      PV_RunJoin_NativePointClaims72.Rows self.columns)
    (terminal : letI : ExternalTypes := types base
      ∀ claims,@host_semantic.point_claims (types base)
        (opsNative base heap box ops runtime world) self.columns point=ok (.Ok claims) →
      ∃ q,@aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        (types base) ops self.«public» claims point self.challenges=ok (.Ok q)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ claims,host_semantic.point_claims self.columns point=ok (.Ok claims) ∧
      Success runtime (.terminal self.«public» claims point self.challenges
        (fun status => .step (PV_RunJoin_SemanticReached69.tail self point claims status) Plan.done)) world ∧
      execute runtime (.terminal self.«public» claims point self.challenges
        (fun status => .step (PV_RunJoin_SemanticReached69.tail self point claims status) Plan.done)) world=
        (do let out ← host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate self point
            ok (out,world)) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨claims,hc⟩ := PV_RunJoin_NativePointClaims72.complete base heap box ops runtime world self.columns point rows
  obtain ⟨q,hq⟩ := terminal claims hc
  exact ⟨claims,hc,
    PV_RunJoin_NativeSemanticPlan69.complete base heap box ops runtime world self point claims q hq,
    PV_RunJoin_SemanticReached69.plan runtime world self point claims hc⟩

#print axioms complete
end R1Z.PV_RunJoin_SemanticPlan72
