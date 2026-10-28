import RPv_FJm_LibraStages
import NDO_JGs_LibraPowers1
import NDO_JGs_LibraTerms1
import NDO_JGs_LibraWrites
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraStage1
open Aeneas Aeneas.Std Result ControlFlow
open JGs_Libra JGs_LibraEnd
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def high : Array Q 4#usize := Array.make 4#usize [q1_0,q1_4,q1_8,q1_12]
theorem powers : FJm_LibraStages.powers (FIo_Install.toWeights JGo_TX2_WeightData.value).extra 1#usize=
    ok (row1,high,q1_4,q1_16) := by
  unfold FJm_LibraStages.powers
  rw [extra1,bind_tc_ok,power1_0,bind_tc_ok,power1_1,bind_tc_ok,power1_2,bind_tc_ok,power1_3,bind_tc_ok]
  have read : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q1_1,q1_2,q1_3]) 2#usize=ok q1_2 := by rfl
  rw [read,bind_tc_ok,power1_4,bind_tc_ok,power1_5,bind_tc_ok,power1_6,bind_tc_ok,power1_7,bind_tc_ok]
  rw [JGs_LibraWrites.one1]
  rfl
#print axioms powers
theorem term0 : FJm_LibraStages.term JGq_Powers1.a4 high 0#usize=ok (0#usize,JGs_Libra.term1_0) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have read : Array.index_usize high 0#usize=ok q1_0 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed1_0,bind_tc_ok,quarter1_0,bind_tc_ok]
#print axioms term0
theorem term1 : FJm_LibraStages.term JGq_Powers1.a4 high 1#usize=ok (3#usize,JGs_Libra.term1_1) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 1#usize=ok 3#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 3#usize=ok JGq_Powers1.p3 := by rfl
  have read : Array.index_usize high 1#usize=ok q1_4 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed1_1,bind_tc_ok,quarter1_1,bind_tc_ok]
#print axioms term1
theorem term2 : FJm_LibraStages.term JGq_Powers1.a4 high 2#usize=ok (2#usize,JGs_Libra.term1_2) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 2#usize=ok 2#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 2#usize=ok JGq_Powers1.p2 := by rfl
  have read : Array.index_usize high 2#usize=ok q1_8 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed1_2,bind_tc_ok,quarter1_2,bind_tc_ok]
#print axioms term2
theorem term3 : FJm_LibraStages.term JGq_Powers1.a4 high 3#usize=ok (1#usize,JGs_Libra.term1_3) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 3#usize=ok 1#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 1#usize=ok JGq_Powers1.p1 := by rfl
  have read : Array.index_usize high 3#usize=ok q1_12 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed1_3,bind_tc_ok,quarter1_3,bind_tc_ok]
#print axioms term3
theorem totals : FJm_LibraStages.totals (Array.make 4#usize [JGs_Libra.term1_0,JGs_Libra.term1_1,JGs_Libra.term1_2,JGs_Libra.term1_3])=
    ok (sum1_2,sum1_3,sum1_4) := by
  have read0 : Array.index_usize (Array.make 4#usize [JGs_Libra.term1_0,JGs_Libra.term1_1,JGs_Libra.term1_2,JGs_Libra.term1_3]) 0#usize=ok JGs_Libra.term1_0 := by rfl
  have read1 : Array.index_usize (Array.make 4#usize [JGs_Libra.term1_0,JGs_Libra.term1_1,JGs_Libra.term1_2,JGs_Libra.term1_3]) 1#usize=ok JGs_Libra.term1_1 := by rfl
  have read2 : Array.index_usize (Array.make 4#usize [JGs_Libra.term1_0,JGs_Libra.term1_1,JGs_Libra.term1_2,JGs_Libra.term1_3]) 2#usize=ok JGs_Libra.term1_2 := by rfl
  have read3 : Array.index_usize (Array.make 4#usize [JGs_Libra.term1_0,JGs_Libra.term1_1,JGs_Libra.term1_2,JGs_Libra.term1_3]) 3#usize=ok JGs_Libra.term1_3 := by rfl
  unfold FJm_LibraStages.totals
  rw [read0,bind_tc_ok,read1,bind_tc_ok,sum1call2,bind_tc_ok,read2,bind_tc_ok,sum1call3,bind_tc_ok,read3,bind_tc_ok,sum1call4,bind_tc_ok]
#print axioms totals
theorem finish : FJm_LibraStages.finish 1#usize JGs_LibraScale1.value 1#usize sum1_2 sum1_3 sum1_4
    q1_4 q1_16 JGq_Powers1.a4 JGs_LibraEnd.middle {start:=2#usize,«end»:=2#usize}=
    ok (.cont ({start:=2#usize,«end»:=2#usize},JGs_LibraEnd.value)) := by
  unfold FJm_LibraStages.finish
  simp only [show ¬(1#usize=0#usize) from by decide,ite_false]
  have ap : Array.index_usize JGq_Powers1.a4 1#usize=ok JGq_Powers1.p1 := by rfl
  rw [JGs_LibraWrites.read,bind_tc_ok,ap,bind_tc_ok,call_d,bind_tc_ok,call_e,bind_tc_ok,call_f,bind_tc_ok,
    JGs_LibraWrites.up2,bind_tc_ok,call_g,bind_tc_ok,call_h,bind_tc_ok,JGs_LibraWrites.up3,bind_tc_ok,
    call_i,bind_tc_ok,power1_8,bind_tc_ok,call_j,bind_tc_ok,JGs_LibraWrites.up4,bind_tc_ok]
#print axioms finish
end AspisR1.JGs_LibraStage1
end
