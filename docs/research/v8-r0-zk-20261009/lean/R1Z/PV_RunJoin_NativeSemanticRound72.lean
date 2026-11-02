import R1Z.PV_RunJoin_NativeRoundPolynomial72
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSemanticRound72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_SampleDomain34
abbrev Q := aspis_core.field.QM31

theorem complete {H S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (digest : aspis_core.digest.Digest32 H)
    (self : @host_semantic.SemanticOracle (types base)) (point : Array Q 10#usize)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (running : Q) (round : Usize) (bound : round.val<10)
    (evaluations : alloc.vec.Vec (core.result.Result Q r1_wire.Error))
    (worker : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      @host_work.map (types base) ops _ _
        (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle)
        (Usize.wrapping_add 100#usize round) (count round)
        (self,point,round,assignments round)=ok evaluations)
    (size : evaluations.length=(count round).val)
    (agrees : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      ∀ i : Usize,i.val<evaluations.length →
      Slice.index_usize (alloc.vec.Vec.deref evaluations) i=
        @host_sumcheck.evaluate_assignment (types base) (opsNative base heap box ops runtime world)
          _ host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle self point round (assignments round) i)
    (rows : letI : ExternalTypes := types base
      PV_RunJoin_NativePointClaims72.Rows self.columns)
    (terminal : letI : ExternalTypes := types base
      ∀ p claims,@host_semantic.point_claims (types base)
        (opsNative base heap box ops runtime world) self.columns p=ok (.Ok claims) →
      ∃ q,@aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        (types base) ops self.«public» claims p self.challenges=ok (.Ok q)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ (polynomial : Nat → Q) (bytes : alloc.vec.Vec U8),
      host_sumcheck.prove_sumcheck_round digest host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle transcript output point running round self=
        PV_RunJoin_RoundAfterPolynomial72.run digest transcript output point running round
          (PV_RunJoin_MergeArray35.array polynomial) ∧
      (∀ k,k<28 → PV_RunJoin_FieldData34.canonical (polynomial k)) ∧
      host_sumcheck.encode_polynomial (PV_RunJoin_MergeArray35.array polynomial)=ok bytes ∧
      bytes.val.length=896 := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  apply PV_RunJoin_NativeRoundPolynomial72.complete base heap box ops runtime world
    digest host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle
    self point transcript output running round bound evaluations worker size agrees
  intro p
  exact PV_RunJoin_SemanticSuff72.complete base heap box ops runtime world self p rows (terminal p)

#print axioms complete
end R1Z.PV_RunJoin_NativeSemanticRound72
