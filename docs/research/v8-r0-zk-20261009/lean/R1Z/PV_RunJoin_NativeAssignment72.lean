import R1Z.PV_RunJoin_NativeSampleSource72
import R1Z.PV_RunJoin_PointRepr72
import R1Z.PV_RunJoin_SemanticSuff72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeAssignment72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {T S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (oi : host_sumcheck.Oracle T) (oracle : T)
    (point : Array Q 10#usize) (round assignments i : Usize)
    (bound : round.val<10) (positive : assignments.val≠0)
    (evaluates : ∀ p,∃ q,oi.evaluate oracle p=ok (.Ok q)) :
    ∃ out,@host_sumcheck.evaluate_assignment (types base) (opsNative base heap box ops runtime world)
      T oi oracle point round assignments i=ok (.Ok out) := by
  obtain ⟨sample,assignment,hs,ha,he⟩ := PV_RunJoin_NativeSampleSource72.reached base heap box ops runtime world
    oi oracle (PV_RunJoin_PointRepr72.cells point) round assignments i bound positive
  rw [PV_RunJoin_PointRepr72.complete] at he
  obtain ⟨out,ho⟩ := evaluates (PV_RunJoin_PointArray34.array
    (ProverCommitSamplePoint49.point (PV_RunJoin_PointRepr72.cells point) round.val assignment
      (UScalar.cast .U32 sample)))
  exact ⟨out,he.trans ho⟩

theorem semantic {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (self : @host_semantic.SemanticOracle (types base)) (point : Array Q 10#usize)
    (round assignments i : Usize) (bound : round.val<10) (positive : assignments.val≠0)
    (rows : letI : ExternalTypes := types base
      PV_RunJoin_NativePointClaims72.Rows self.columns)
    (terminal : letI : ExternalTypes := types base
      ∀ p claims,@host_semantic.point_claims (types base)
        (opsNative base heap box ops runtime world) self.columns p=ok (.Ok claims) →
      ∃ q,@aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        (types base) ops self.«public» claims p self.challenges=ok (.Ok q)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ out,host_sumcheck.evaluate_assignment
      host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle
      self point round assignments i=ok (.Ok out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  apply complete base heap box ops runtime world _ self point round assignments i bound positive
  intro p
  exact PV_RunJoin_SemanticSuff72.complete base heap box ops runtime world self p rows (terminal p)

#print axioms complete
#print axioms semantic
end R1Z.PV_RunJoin_NativeAssignment72
