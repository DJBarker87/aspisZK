import NDO_JGq_High0
import NDO_JGq_High2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_SharedHigh
open Aeneas Aeneas.Std Result
open JGq_High
abbrev E := FIo_Install.NE
def row0 := FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) JGo_TX2_WeightData.r0_5
def row2 := FIn_WeightsInstall.mapArray (FIn_WeightsInstall.mapArray FIo_Install.toQ) JGo_TX2_WeightData.r2_5

theorem scale_mul : FIo_Native.aspis_core.field.wide_exact.WideExact.mul JGq_Scale0.value JGq_Scale1.value=ok scale := by with_unfolding_all rfl
#print axioms scale_mul
theorem mul0 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale high0=ok value0 := by with_unfolding_all rfl
#print axioms mul0
theorem mul2 : FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale high2=ok value2 := by with_unfolding_all rfl
#print axioms mul2

def write (before : Array E 7#usize) : Array E 7#usize := (before.set 1#usize value0).set 3#usize value2

/-- Actual shared_high on the retained operands, for any earlier regular parts.
The earlier parts are preserved except the two source-assigned slots. -/
theorem source (before : Array E 7#usize) :
    FIo_Native.weights.shared_high JGq_SharedPartials.value JGq_Common.w JGq_Powers0.a4 JGq_Powers1.a4 before=
      ok (.Ok (),write before) := by
  have r0 : Array.index_usize JGq_Common.w.factors 0#usize=ok row0 := by rfl
  have r2 : Array.index_usize JGq_Common.w.factors 2#usize=ok row2 := by rfl
  have r00 : Array.index_usize row0 0#usize=ok JGq_Scale0.row := by rfl
  have r01 : Array.index_usize row0 1#usize=ok JGq_Scale1.row := by rfl
  have r04 : Array.index_usize row0 4#usize=ok JGq_High.row0 := by rfl
  have r20 : Array.index_usize row2 0#usize=ok JGq_Scale0.row := by rfl
  have r21 : Array.index_usize row2 1#usize=ok JGq_Scale1.row := by rfl
  have r24 : Array.index_usize row2 4#usize=ok JGq_High.row2 := by rfl
  obtain ⟨⟨old,back⟩,idx,_,hb⟩ := WP.spec_imp_exists
    (Array.index_mut_usize_spec before 1#usize (by scalar_tac))
  subst back
  obtain ⟨after,updated,ha⟩ := WP.spec_imp_exists
    (Array.update_spec (before.set 1#usize value0) 3#usize value2 (by scalar_tac))
  subst after
  unfold FIo_Native.weights.shared_high
  rw [r0,bind_tc_ok,r04,bind_tc_ok,source0,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rw [r00,bind_tc_ok,JGq_Scale0.source,bind_tc_ok,r01,bind_tc_ok,JGq_Scale1.source,bind_tc_ok,
    scale_mul,bind_tc_ok,mul0,bind_tc_ok,idx,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [r2,bind_tc_ok,r24,bind_tc_ok,source2,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rw [r20,bind_tc_ok,JGq_Scale0.source,bind_tc_ok,r21,bind_tc_ok,JGq_Scale1.source,bind_tc_ok,
    scale_mul,bind_tc_ok,mul2,bind_tc_ok,updated,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGq_SharedHigh
end
