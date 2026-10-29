import R1Z.PV_RunJoin_BuildMaterialStored58
import R1Z.PV_RunJoin_CoefficientsActual50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BuildMaterialCoefficients58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (public1 : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (types base))
    (compiled : @aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1 (types base))
    (noised : aspis_statement.state_only_trace.StateOnlyTraceFoundation)
    (maskOnly : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
    (d g padding : Array aspis_core.field.QM31 1024#usize)
    (start backend : prover.Backend) (hash : H) (variant : transport.Variant)
    (built : host_semantic.BuiltSemantics H) (length : start.messages.length=29)
    (success : @host_semantic.build_with_material (types base) (selected base heap box ops)
      H prover.Backend D
      (@prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments (types base) (selected base heap box ops))
      public1 compiled noised maskOnly d g padding start hash variant=ok (.Ok built,backend)) :
    ∃ coeff : alloc.vec.Vec PV_RunJoin_CoefficientActualCell50.Column,
      @prover.opening_coefficients (types base) (selected base heap box ops) .S2
        (alloc.vec.Vec.deref backend.messages)=ok coeff ∧
      coeff.val=backend.messages.val.map PV_RunJoin_CoefficientActualCell50.permuted ∧
      coeff.length=29 := by
  have stored := PV_RunJoin_BuildMaterialStored58.complete base heap box ops D
    public1 compiled noised maskOnly d g padding start backend hash variant built length success
  have small : (alloc.vec.Vec.deref backend.messages).length≤14336 := by
    change backend.messages.length≤14336
    rw [stored.2.2]
    omega
  obtain ⟨coeff,run,values,len⟩ := PV_RunJoin_CoefficientsActual50.complete base heap box ops
    (alloc.vec.Vec.deref backend.messages) small
  exact ⟨coeff,run,values,len.trans stored.2.2⟩

#print axioms complete
end R1Z.PV_RunJoin_BuildMaterialCoefficients58
