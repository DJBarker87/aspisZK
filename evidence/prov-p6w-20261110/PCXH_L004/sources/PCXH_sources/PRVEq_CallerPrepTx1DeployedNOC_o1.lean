import Aeneas
import NNH_CorrectConfiguration
import NNH_HostSeed
import NJG_CallerInstall
import NNH_HostCtx
import NNH_Tx2SourceConfiguration
import NOC_Run5bHost
import NOC_PrepareFront
import PRVEq_CallerPrepTx1_o1
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1
set_option autoImplicit false
noncomputable section
namespace PCVP_C
open AspisR1CurrentCaller.PCVK_C_o1

-- Usize literal arithmetic (System.Platform.numBits is opaque, so rfl cannot evaluate; every value used here is below 2^32)
theorem addlit (a b c : Std.Usize) (h : a.val + b.val = c.val) (hc : c.val < 4294967296) :
    (a + b : Result Std.Usize) = ok c := by
  have hmax : a.val + b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.add_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem mullit (a b c : Std.Usize) (h : a.val * b.val = c.val) (hc : c.val < 4294967296) :
    (a * b : Result Std.Usize) = ok c := by
  have hmax : a.val * b.val ≤ Std.Usize.max := by scalar_tac
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.mul_spec (x := a) (y := b) hmax)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem sublit (a b c : Std.Usize) (h : a.val - b.val = c.val) (hb : b.val ≤ a.val) :
    (a - b : Result Std.Usize) = ok c := by
  obtain ⟨z, hz, hv⟩ := Aeneas.Std.WP.spec_imp_exists (Usize.sub_spec (x := a) (y := b) hb)
  rw [hz]; congr 1; apply UScalar.eq_of_val_eq; omega

theorem v_SEMANTIC_COMPACT_VALUES : compact.SEMANTIC_COMPACT_VALUES = ok 426#usize := by
  unfold compact.SEMANTIC_COMPACT_VALUES
  rw [mullit 10#usize 28#usize 280#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 1#usize 280#usize 281#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 87#usize 29#usize 116#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 281#usize 116#usize 397#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 397#usize 29#usize 426#usize (by scalar_tac) (by scalar_tac)]

theorem v_SEMANTIC_BYTES : verifier.SEMANTIC_BYTES = ok 13831#usize := by
  unfold verifier.SEMANTIC_BYTES
  rw [mullit 29#usize 32#usize 928#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [addlit 12903#usize 928#usize 13831#usize (by scalar_tac) (by scalar_tac)]

theorem v_COMPACT_SEMANTIC : compact.COMPACT_SEMANTIC = ok 7015#usize := by
  unfold compact.COMPACT_SEMANTIC compact.LOGICAL_SEMANTIC
  rw [v_SEMANTIC_COMPACT_VALUES]
  simp only [bind_tc_ok]
  rw [mullit 16#usize 426#usize 6816#usize (by scalar_tac) (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [v_SEMANTIC_BYTES]
  simp only [bind_tc_ok]
  rw [sublit 13831#usize 6816#usize 7015#usize (by scalar_tac) (by scalar_tac)]

theorem v_OFF_Y1 : compact.OFF_Y1 = ok 7031#usize := by
  unfold compact.OFF_Y1
  rw [v_COMPACT_SEMANTIC]
  simp only [bind_tc_ok]
  unfold compact.OFF_SEMANTIC compact.HEADER
  rw [addlit 16#usize 7015#usize 7031#usize (by scalar_tac) (by scalar_tac)]

theorem v_COMPACT_Y1 : compact.COMPACT_Y1 = ok 464#usize := by
  unfold compact.COMPACT_Y1
  rw [mullit 29#usize 16#usize 464#usize (by scalar_tac) (by scalar_tac)]

theorem v_OFF_INACTIVE : compact.OFF_INACTIVE = ok 7495#usize := by
  unfold compact.OFF_INACTIVE
  rw [v_OFF_Y1]; simp only [bind_tc_ok]
  rw [v_COMPACT_Y1]; simp only [bind_tc_ok]
  rw [addlit 7031#usize 464#usize 7495#usize (by scalar_tac) (by scalar_tac)]

theorem v_OFF_ROUND0 : compact.OFF_ROUND0 = ok 7527#usize := by
  unfold compact.OFF_ROUND0
  rw [v_OFF_INACTIVE]; simp only [bind_tc_ok]
  rw [addlit 7495#usize 32#usize 7527#usize (by scalar_tac) (by scalar_tac)]

theorem v_OFF_FOLDED_ROOT : compact.OFF_FOLDED_ROOT = ok 7751#usize := by
  unfold compact.OFF_FOLDED_ROOT
  rw [v_OFF_ROUND0]; simp only [bind_tc_ok]
  rw [addlit 7527#usize 224#usize 7751#usize (by scalar_tac) (by scalar_tac)]

theorem v_OFF_ROUND1 : compact.OFF_ROUND1 = ok 7783#usize := by
  unfold compact.OFF_ROUND1
  rw [v_OFF_FOLDED_ROOT]; simp only [bind_tc_ok]
  rw [addlit 7751#usize 32#usize 7783#usize (by scalar_tac) (by scalar_tac)]


/-- The externals read off the Ops; the six constant fields are the fresh definitions. -/
def xOf (ops : AspisR1CurrentCaller.Ops) : Ext := {
    aspis_core_field_wide_exact_WideExact_ZERO := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO ops
    verifier_candidate_canonical_scan := ops.op4
    verifier_QueryGeometry_for_range := ops.op19
    verifier_candidate_batch_merkle := @ops.op6
    verifier_candidate_parse_shape := ops.op3
    verifier_BatchedWeights_finish := ops.op17
    verifier_candidate_query_loop := ops.op7
    verifier_candidate_wide_view := ops.op5
    r1_semantic_verify_observed := @ops.op9
    verifier_BatchedWeights_new := ops.op18
    aspis_core_r0_heap_filled := @ops.op1
    verifier_Accumulator_new := ops.op20
    compact_expand_semantic := ops.op10
    verifier_Prepared_new := @ops.op8
    compact_expand_values := ops.op11
    verifier_checkpoint := @ops.op16
    verifier_mark := AspisR1CurrentCaller.verifier.mark
  }

theorem bound (ops : AspisR1CurrentCaller.Ops)
    (h2 : ops.op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse)
    (h12 : ops.op12 = ok 16#usize) (h13 : ops.op13 = ok 7015#usize) (h14 : ops.op14 = ok 464#usize)
    (h15 : ops.op15 = ok 13831#usize) (h21 : ops.op21 = ok 7527#usize) : Bound ops (xOf ops) := by
  have c2 : ops.op2 = AspisR1CurrentCaller.PCVK_C_o1.verifier.Error.Insts.CoreConvertFromCodecError.from := by rw [h2]; rfl
  have c12 : ops.op12 = ok AspisR1CurrentCaller.PCVK_C_o1.compact.OFF_SEMANTIC := by rw [h12]; with_unfolding_all rfl
  have c13 : ops.op13 = AspisR1CurrentCaller.PCVK_C_o1.compact.COMPACT_SEMANTIC := by rw [h13, v_COMPACT_SEMANTIC]
  have c14 : ops.op14 = AspisR1CurrentCaller.PCVK_C_o1.compact.COMPACT_Y1 := by rw [h14, v_COMPACT_Y1]
  have c15 : ops.op15 = AspisR1CurrentCaller.PCVK_C_o1.compact.LOGICAL_SEMANTIC := by
    rw [h15]; unfold AspisR1CurrentCaller.PCVK_C_o1.compact.LOGICAL_SEMANTIC; rw [v_SEMANTIC_BYTES]
  have c21 : ops.op21 = AspisR1CurrentCaller.PCVK_C_o1.compact.OFF_ROUND0 := by rw [h21, v_OFF_ROUND0]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, c2, c12, c13, c14, c15, c21⟩

theorem generic_prepare (ops : AspisR1CurrentCaller.Ops)
    (h2 : ops.op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse)
    (h12 : ops.op12 = ok 16#usize) (h13 : ops.op13 = ok 7015#usize) (h14 : ops.op14 = ok 464#usize)
    (h15 : ops.op15 = ok 13831#usize) (h21 : ops.op21 = ok 7527#usize) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (xOf ops) H = @AspisR1CurrentCaller.verifier.candidate.prepare ops H :=
  PRVEq.CallerPrepTx1_k1.verifier_candidate_prepare_eq (bound ops h2 h12 h13 h14 h15 h21) H

theorem generic_tx1 (ops : AspisR1CurrentCaller.Ops)
    (h2 : ops.op2 = fun _ => ok AspisR1CurrentCaller.verifier.Error.Parse)
    (h12 : ops.op12 = ok 16#usize) (h13 : ops.op13 = ok 7015#usize) (h14 : ops.op14 = ok 464#usize)
    (h15 : ops.op15 = ok 13831#usize) (h21 : ops.op21 = ok 7527#usize) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (xOf ops) H = @AspisR1CurrentCaller.verifier.candidate.tx1 ops H :=
  PRVEq.CallerPrepTx1_k1.verifier_candidate_tx1_eq (bound ops h2 h12 h13 h14 h15 h21) H

section
variable (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
  (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

/-- The deployed CurrentCompact Ops of the credited host context. -/
abbrev cur := DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration missing env err r)

theorem deployed_prepare (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (xOf (cur missing env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (cur missing env err r) H :=
  generic_prepare _ rfl rfl rfl rfl rfl rfl H

theorem deployed_tx1 (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (xOf (cur missing env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (cur missing env err r) H :=
  generic_tx1 _ rfl rfl rfl rfl rfl rfl H
end

theorem deployed_prepare_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (xOf (cur NNH_HostSeed.m0 env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (cur NNH_HostSeed.m0 env err r) H :=
  deployed_prepare _ _ _ _ H

theorem deployed_tx1_m0 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (xOf (cur NNH_HostSeed.m0 env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (cur NNH_HostSeed.m0 env err r) H :=
  deployed_tx1 _ _ _ _ H

/-- The packet Ops of the credited emitted-tx1 chain (NHL_DriverModel): every base/expected/reserved. -/
theorem packet_prepare (base expected : AspisR1CurrentCaller.Ops) (reserved : Bool) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (xOf (NHL_DriverModel.preparedOps base expected reserved)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (NHL_DriverModel.preparedOps base expected reserved) H :=
  generic_prepare _ rfl rfl rfl rfl rfl rfl H

theorem packet_tx1 (base expected : AspisR1CurrentCaller.Ops) (reserved : Bool) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (xOf (NHL_DriverModel.txOps base expected reserved)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (NHL_DriverModel.txOps base expected reserved) H :=
  generic_tx1 _ rfl rfl rfl rfl rfl rfl H

/-- Composition with the existing NJG_CallerInstall.tx1 (emitted tx1 = gate tx1 at the packet Ops):
the PCVK fresh frozen tx1 at xOf equals NHW_EmittedTx1.tx1 at the installed packet Ops. -/
theorem njg_tx1 (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice Std.U8) (k : Std.Usize) (hash : H) :
    NHW_EmittedTx1.tx1
      (NHL_Packets.installed
        (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
          (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std)) reserved)
      (NHW_EmittedPrepare.prepare
        (NHL_Packets.installed
          (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
            (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std)) reserved))
      D pubdata publicBytes proof k hash none =
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1
      (xOf (NHL_DriverModel.txOps
        (NHW_DriverInstantiation.packetOps (NJG_CurrentEquation.ops base seed std)
          (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std))
        (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std) reserved)) H
      D pubdata publicBytes proof k hash none := by
  rw [packet_tx1]
  exact NJG_CallerInstall.tx1 base reserved seed std D pubdata publicBytes proof k hash

theorem njg_prepare (base : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (seed : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pubdata : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H) (g : NHL_PrepareStages.Scratch) :
    NHL_EmittedPrepare.prepare
      (NHL_Packets.installed (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std)) reserved)
      D pubdata proof hash none g =
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare
      (xOf (NHL_PrepareModel.children
        (NHL_Packets.installed (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std)) reserved)
        (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std))) H
      D pubdata proof hash none g := by
  have := packet_prepare (NHW_Prepare.nativeChildren (NJG_CurrentEquation.ops base seed std))
    (RowShape_InstalledSlots.verifierOps (NJG_CurrentEquation.ops base seed std) (FIp_Install.boundaries seed) std) reserved H
  unfold NHL_DriverModel.preparedOps at this
  rw [this]
  exact NJG_CallerInstall.prepare base reserved seed std D pubdata proof hash g


/-! ## Corrected seed: the headline's host context NOC_HostCtx / NOC_HostSeed.m0

Seed-generic: `generic_prepare`/`generic_tx1` take any Ops with the six Bound constant fields, so the statements
below hold for the Ops `currentInstalled (NOC_HostCtx.configuration c)` of every host context `c`, hence for every
`(NOC_HostSeed.m0 reserved)` and any later re-instantiation of the seed whose six constant fields are rfl-equal. -/
abbrev curN {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  DrvC_Installation.currentInstalled (AspisR1.NOC_HostCtx.configuration c)

theorem noc_prepare {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (xOf (curN c)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (curN c) H :=
  generic_prepare _ rfl rfl rfl rfl rfl rfl H

theorem noc_tx1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.tx1 (xOf (curN c)) H =
      @AspisR1CurrentCaller.verifier.candidate.tx1 (curN c) H :=
  generic_tx1 _ rfl rfl rfl rfl rfl rfl H

/-- Seed-generic over the uninstalled seed `m` (any NOC_HostSeed-like seed). -/
theorem seed_prepare (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (H : Type) :
    @AspisR1CurrentCaller.PCVK_C_o1.verifier.candidate.prepare (xOf (cur m env err r)) H =
      @AspisR1CurrentCaller.verifier.candidate.prepare (cur m env err r) H :=
  deployed_prepare _ _ _ _ H

/-- Non-vacuity at the corrected seed: the installed op1 is NOC_HostSeed.filled (not the divergent residual). -/
theorem noc_op1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    @AspisR1CurrentCaller.Ops.op1 (curN c) = @AspisR1.NOC_HostSeed.filled (NNH_HostCtx.envOf c).reservation := rfl

/-- On a granted reservation op1 returns Ok (zeros n); cited from NOC_PrepareFront.filled, not re-proved. -/
theorem noc_op1_filled {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (n : Std.Usize)
    (granted : (NNH_HostCtx.envOf c).reservation = true) :
    (curN c).op1 core.marker.CopyU8 n 0#u8 = ok (.Ok (AspisR1.NOC_PrepareFront.zeros n)) :=
  AspisR1.NOC_PrepareFront.filled c n granted

theorem noc_op1_ne_div {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (n : Std.Usize)
    (granted : (NNH_HostCtx.envOf c).reservation = true) :
    (curN c).op1 core.marker.CopyU8 n 0#u8 ≠ Result.div := by
  rw [noc_op1_filled c n granted]; intro h; cases h

/-- Contrast: at the old NNH_HostSeed.m0 the same slot is the divergent residual. -/
theorem old_op1_div (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
    (n : Std.Usize) (x : Std.U8) :
    (cur NNH_HostSeed.m0 env err r).op1 core.marker.CopyU8 n x = Result.div := rfl

#print axioms noc_prepare
#print axioms noc_tx1
#print axioms seed_prepare
#print axioms noc_op1
#print axioms noc_op1_filled
#print axioms noc_op1_ne_div
#print axioms old_op1_div
end PCVP_C
