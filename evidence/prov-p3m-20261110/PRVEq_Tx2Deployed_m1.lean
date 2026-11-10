-- PCVM_ phase P3m, scope 1: the deployed VTop Ops (DrvI_Installation.stage over the NNH Tx2 stage seed) against the Bound of PRVEq_VTop_l1.
-- Statement shape: the ten callee fields of Bound are instantiated by the deployed Ops fields themselves (xdep); the constant fields are proved
-- (with_unfolding_all rfl) against the fresh compact constants; op18 (resume) is a retained hypothesis.
import Aeneas
import PRVEq_VTop_l1
import RPz7_DrvI_Installation
import RPz7_AuS1_Install
import NHT_Constants
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVM_Tx2Deployed
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1

-- NNH_Tx2SourceConfiguration.stage with its two slot values (NJC_ClosedCalls.inactive, NHV_ReleaseOps.mark) as parameters
-- (those modules come from a different seed generation and do not import together with the DrvI chain; see PCVM_CLASSIFICATIONS.json)
-- text-identical copy of NHT_Tx2CommonModel.constants (that module does not import together with the DrvI chain here)
def constants (ops : VTop_Stages.Ops) : VTop_Stages.Ops := {ops with
 op0 := @NHT_Constants.core.option.Option.ok_or
 op14 := NHT_Constants.compact.OFF_ROUND1
 op15 := NHT_Constants.compact.OFF_FOLDED_ROOT
 op16 := ok NHT_Constants.compact.SPLIT
 op20 := NHT_Constants.compact.OFF_OPENINGS
 op21 := NHT_Constants.compact.OFF_FINAL
 op22 := NHT_Constants.compact.OFF_ROUND0
 op23 := NHT_Constants.compact.OFF_INACTIVE
 unwrap32 := core.result.Result.unwrap core.fmt.DebugTryFromSliceError }

def stageNNH (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
    (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit)
    (base : VTop_Stages.Ops) : VTop_Stages.Ops :=
  constants {base with op2 := inact, op13 := mk}

def Dep {F CE : Type} (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
    (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) : VTop_Stages.Ops :=
  DrvI_Installation.stage reserved query geo (AuS1_Install.base (stageNNH inact mk base)) finish

def xdep (y : Ext) (d : VTop_Stages.Ops) : Ext :=
  { y with
    aspis_core_field_wide_exact_WideExact_from_le_bytes := @d.op2
    verifier_candidate_parse_shape := @d.op3
    verifier_candidate_batch_merkle := @d.op5
    verifier_candidate_query_loop := @d.op6
    verifier_BatchedWeights_finish := @d.op9
    verifier_BatchedWeights_new := @d.op10
    verifier_QueryGeometry_for_range := @d.op11
    verifier_mark := @d.op13
    weights_powers := @d.op17
    verifier_finish_relation := @d.op19 }


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

#print axioms v_OFF_ROUND1
#print axioms v_OFF_FOLDED_ROOT

section
variable {F CE : Type} (inact : Slice Std.U8 → Result (Option aspis_core.field.wide_exact.WideExact))
  (mk : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit) (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

-- the gate item each callee slot stands for (definitional)
theorem slot_op2 : (Dep inact mk reserved query geo base finish).op2 = inact := rfl
theorem slot_op3 : (Dep inact mk reserved query geo base finish).op3 = Tx2I_Install.shape := rfl
theorem slot_op5 : @(Dep inact mk reserved query geo base finish).op5 = @Op5T_Install.stageBatch Port4B_Install.leaves := rfl
theorem slot_op6 : (Dep inact mk reserved query geo base finish).op6 =
    Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query)) := rfl
theorem slot_op9 : (Dep inact mk reserved query geo base finish).op9 = Port3_FlushInstall.flush := rfl
theorem slot_op10 : (Dep inact mk reserved query geo base finish).op10 = Port3_NativePendingInstall.source reserved := rfl
theorem slot_op11 : (Dep inact mk reserved query geo base finish).op11 =
    Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geo) := rfl
theorem slot_op13 : (Dep inact mk reserved query geo base finish).op13 = mk := rfl
theorem slot_op17 : (Dep inact mk reserved query geo base finish).op17 = Tx2N_Powers.powers := rfl
theorem slot_op19 : (Dep inact mk reserved query geo base finish).op19 = Port4D_FinishInstall.finish finish := rfl
theorem slot_op18 : @(Dep inact mk reserved query geo base finish).op18 = @Port4A_ReaderInstall.reader reserved := rfl

-- constant fields
theorem c_op0 : @(Dep inact mk reserved query geo base finish).op0 = @core.option.Option.ok_or := by
  with_unfolding_all rfl
theorem c_op20 : (Dep inact mk reserved query geo base finish).op20 = compact.OFF_OPENINGS := by
  with_unfolding_all rfl
theorem c_op21 : (Dep inact mk reserved query geo base finish).op21 = compact.OFF_FINAL := by
  with_unfolding_all rfl
theorem c_op22 : (Dep inact mk reserved query geo base finish).op22 = compact.OFF_ROUND0 := by
  with_unfolding_all rfl
theorem c_op23 : (Dep inact mk reserved query geo base finish).op23 = compact.OFF_INACTIVE := by
  with_unfolding_all rfl
theorem c_op16 : (Dep inact mk reserved query geo base finish).op16 = ok compact.SPLIT := by
  with_unfolding_all rfl
theorem c_op14 : (Dep inact mk reserved query geo base finish).op14 = compact.OFF_ROUND1 := by
  rw [v_OFF_ROUND1]; rfl
theorem c_op15 : (Dep inact mk reserved query geo base finish).op15 = compact.OFF_FOLDED_ROOT := by
  rw [v_OFF_FOLDED_ROOT]; rfl
theorem c_unwrap32 : (Dep inact mk reserved query geo base finish).unwrap32 =
    fun r => core.result.Result.unwrap core.fmt.DebugTryFromSliceError r := by
  funext r; cases r <;> rfl

/-- The deployed Bound: every field of Bound except op18 (resume) holds for the deployed Ops against the externals xdep. -/
theorem deployed_bound (y : Ext)
    (h18 : @(Dep inact mk reserved query geo base finish).op18 =
      @verifier.resume (xdep y (Dep inact mk reserved query geo base finish))) :
    Bound (Dep inact mk reserved query geo base finish) (xdep y (Dep inact mk reserved query geo base finish)) :=
  ⟨c_op0 inact mk reserved query geo base finish, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   c_op14 inact mk reserved query geo base finish, c_op15 inact mk reserved query geo base finish,
   c_op16 inact mk reserved query geo base finish, rfl, h18, rfl,
   c_op20 inact mk reserved query geo base finish, c_op21 inact mk reserved query geo base finish,
   c_op22 inact mk reserved query geo base finish, c_op23 inact mk reserved query geo base finish,
   c_unwrap32 inact mk reserved query geo base finish⟩

theorem deployed_tx2_common (y : Ext)
    (h18 : @(Dep inact mk reserved query geo base finish).op18 =
      @verifier.resume (xdep y (Dep inact mk reserved query geo base finish)))
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_common (xdep y (Dep inact mk reserved query geo base finish)) inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_common (Dep inact mk reserved query geo base finish) inst public_bytes proof checkpoint hash obs :=
  eq_tx2_common _ _ (deployed_bound inact mk reserved query geo base finish y h18) inst public_bytes proof checkpoint hash obs

theorem deployed_tx2_authenticated (y : Ext)
    (h18 : @(Dep inact mk reserved query geo base finish).op18 =
      @verifier.resume (xdep y (Dep inact mk reserved query geo base finish)))
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_authenticated (xdep y (Dep inact mk reserved query geo base finish)) inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_authenticated (Dep inact mk reserved query geo base finish) inst public_bytes proof checkpoint hash obs :=
  eq_tx2_authenticated _ _ (deployed_bound inact mk reserved query geo base finish y h18) inst public_bytes proof checkpoint hash obs
end

#print axioms c_op0
#print axioms c_op20
#print axioms c_op21
#print axioms c_op22
#print axioms c_op23
#print axioms c_op16
#print axioms c_op14
#print axioms c_op15
#print axioms c_unwrap32
#print axioms deployed_bound
#print axioms deployed_tx2_common
#print axioms deployed_tx2_authenticated
end PCVM_Tx2Deployed
