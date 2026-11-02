import R1Z.PV_RunJoin_BridgeObstruction73
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ExactBridgeObstruction73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (terminal : @PV_RunJoin_OracleBridge38.Terminal (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

/-- The diagnostic satisfies precisely the original consumer's forall-claims
hypothesis, and therefore its source evaluation equality, while P is empty.
This does not assert DeployedWrapper557 or describe the deployed dictionary. -/
theorem complete (self : @host_semantic.SemanticOracle (types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := types base
    let candidate := PV_RunJoin_BridgeObstruction73.diagnostic base ops terminal
    let native := opsNative base heap box candidate runtime world
    (∀ claims,native.op227 self.«public» claims point self.challenges=
      terminal self.«public» claims point self.challenges) ∧
    @host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
      (types base) native self point=
      @PV_RunJoin_OracleBridge38.withTerminal (types base) native terminal self point ∧
    ¬Nonempty (PV_RunJoin_NativeActual63.P base heap box candidate runtime world) := by
  letI : ExternalTypes := types base
  let candidate := PV_RunJoin_BridgeObstruction73.diagnostic base ops terminal
  let native := opsNative base heap box candidate runtime world
  have callback : ∀ claims,native.op227 self.«public» claims point self.challenges=
      terminal self.«public» claims point self.challenges := by
    intro claims
    rw [PV_RunJoin_BridgeObstruction73.callback]
  exact ⟨callback,PV_RunJoin_OracleBridge38.selected_callback native terminal self point callback,
    PV_RunJoin_BridgeObstruction73.no_capture base heap box ops terminal runtime world⟩

#print axioms complete
end R1Z.PV_RunJoin_ExactBridgeObstruction73
