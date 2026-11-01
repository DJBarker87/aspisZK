import R1Z.PV_RunJoin_ClaimMaskTotal69
import R1Z.PV_RunJoin_NativeExtraTotal69
import R1Z.PV_RunJoin_SemanticReached69
import R1Z.PV_RunJoin_PreparedMapErr48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSemanticSuff69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem tail {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (self : @host_semantic.SemanticOracle (types base)) (point : Array Q 10#usize)
    (claims : Array (Array Q 29#usize) 3#usize) (terminal : Q) :
    ∃ out,@PV_RunJoin_SemanticReached69.tail (types base) (opsNative base heap box ops runtime world)
      self point claims (.Ok terminal)=ok (.Ok out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have hmap : core.result.Result.map_err
      host_semantic.OracleSemanticOracle.evaluate.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
      (.Ok terminal) ()=ok (.Ok terminal) := by
    change @ExternalFuns.op12 (types base) (opsNative base heap box ops runtime world) _ _ _ _ _ _ _=_
    rw [PV_RunJoin_PreparedMapErr48.field (PV_RunJoin_NativeResidual62.baseTypes base) heap box
      (residual base ops runtime world)]
    rfl
  obtain ⟨c,hc⟩ := ProverRwP6ArrayRead.read claims 0#usize (by decide)
  obtain ⟨mask,hm⟩ := @PV_RunJoin_ClaimMaskTotal69.complete (types base)
    (opsNative base heap box ops runtime world)
    ⟨_,PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world⟩
    (PV_RunJoin_NativeMaskValueTotal69.complete base heap box ops runtime world) c point
  obtain ⟨q,hq⟩ := PV_RunJoin_NativeQuarticTotal69.mul base heap box ops runtime world self.eta terminal
  obtain ⟨q1,hq1⟩ := PV_RunJoin_NativeQuarticTotal69.add base heap box ops runtime world mask q
  obtain ⟨q2,hq2⟩ := ProverRwP6ArrayRead.read point 8#usize (by decide)
  obtain ⟨q3,hq3⟩ := ProverRwP6ArrayRead.read point 9#usize (by decide)
  obtain ⟨extra,he⟩ := PV_RunJoin_NativeExtraTotal69.complete base heap box ops runtime world self.d q2 q3
  obtain ⟨out,ho⟩ := PV_RunJoin_NativeQuarticTotal69.add base heap box ops runtime world q1 extra
  exact ⟨out,by simp only [PV_RunJoin_SemanticReached69.tail,hmap,
    core.result.Result.Insts.CoreOpsTry.branch,hc,hm,hq,hq1,hq2,hq3,he,ho,bind_tc_ok]⟩

/-- Sufficient op227 condition is on the EXACT point_claims result reached by
this evaluator. The original residual callback is retained via its native frame.
Point-claim success is still local input provenance, not a capture-success law. -/
theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (self : @host_semantic.SemanticOracle (types base)) (point : Array Q 10#usize)
    (claims : Array (Array Q 29#usize) 3#usize)
    (hc : @host_semantic.point_claims (types base) (opsNative base heap box ops runtime world)
      self.columns point=ok (.Ok claims))
    (terminal : Q)
    (ht : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (types base) ops self.«public» claims point self.challenges=ok (.Ok terminal)) :
    ∃ out,@host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
      (types base) (opsNative base heap box ops runtime world) self point=ok (.Ok out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have ht' : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      self.«public» claims point self.challenges=ok (.Ok terminal) := by
    change @ExternalFuns.op227 (types base) (opsNative base heap box ops runtime world) _ _ _ _=_
    rw [PV_RunJoin_NativeFrames63.op227]
    exact ht
  rw [PV_RunJoin_SemanticReached69.reached self point claims hc,ht',bind_tc_ok]
  exact tail base heap box ops runtime world self point claims terminal

#print axioms tail
#print axioms complete
end R1Z.PV_RunJoin_NativeSemanticSuff69
