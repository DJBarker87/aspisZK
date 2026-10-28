import RPv_FJm_LibraStages
import NDO_JGs_LibraPowers0
import NDO_JGs_LibraTerms0
import NDO_JGs_LibraWrites
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraStage0
open Aeneas Aeneas.Std Result ControlFlow
open JGs_Libra JGs_LibraEnd
abbrev E := FIo_Install.NE
abbrev Q := FIo_Install.NQ
def high : Array Q 4#usize := Array.make 4#usize [q0_0,q0_4,q0_8,q0_12]
theorem powers : FJm_LibraStages.powers (FIo_Install.toWeights JGo_TX2_WeightData.value).extra 0#usize=
    ok (row0,high,q0_4,q0_16) := by
  unfold FJm_LibraStages.powers
  rw [extra0,bind_tc_ok,power0_0,bind_tc_ok,power0_1,bind_tc_ok,power0_2,bind_tc_ok,power0_3,bind_tc_ok]
  have read : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_1,q0_2,q0_3]) 2#usize=ok q0_2 := by rfl
  rw [read,bind_tc_ok,power0_4,bind_tc_ok,power0_5,bind_tc_ok,power0_6,bind_tc_ok,power0_7,bind_tc_ok]
  rw [JGs_LibraWrites.one0]
  rfl
#print axioms powers
theorem term0 : FJm_LibraStages.term JGq_Powers1.a4 high 0#usize=ok (0#usize,JGs_Libra.term0_0) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have read : Array.index_usize high 0#usize=ok q0_0 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed0_0,bind_tc_ok,quarter0_0,bind_tc_ok]
#print axioms term0
theorem term1 : FJm_LibraStages.term JGq_Powers1.a4 high 1#usize=ok (3#usize,JGs_Libra.term0_1) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 1#usize=ok 3#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 3#usize=ok JGq_Powers1.p3 := by rfl
  have read : Array.index_usize high 1#usize=ok q0_4 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed0_1,bind_tc_ok,quarter0_1,bind_tc_ok]
#print axioms term1
theorem term2 : FJm_LibraStages.term JGq_Powers1.a4 high 2#usize=ok (2#usize,JGs_Libra.term0_2) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 2#usize=ok 2#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 2#usize=ok JGq_Powers1.p2 := by rfl
  have read : Array.index_usize high 2#usize=ok q0_8 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed0_2,bind_tc_ok,quarter0_2,bind_tc_ok]
#print axioms term2
theorem term3 : FJm_LibraStages.term JGq_Powers1.a4 high 3#usize=ok (1#usize,JGs_Libra.term0_3) := by
  have perm : Array.index_usize FIo_Native.weights.PERM 3#usize=ok 1#usize := by with_unfolding_all rfl
  have ap : Array.index_usize JGq_Powers1.a4 1#usize=ok JGq_Powers1.p1 := by rfl
  have read : Array.index_usize high 3#usize=ok q0_12 := by rfl
  unfold FJm_LibraStages.term
  rw [perm,bind_tc_ok,ap,bind_tc_ok,read,bind_tc_ok,mixed0_3,bind_tc_ok,quarter0_3,bind_tc_ok]
#print axioms term3
theorem totals : FJm_LibraStages.totals (Array.make 4#usize [JGs_Libra.term0_0,JGs_Libra.term0_1,JGs_Libra.term0_2,JGs_Libra.term0_3])=
    ok (sum0_2,sum0_3,sum0_4) := by
  have read0 : Array.index_usize (Array.make 4#usize [JGs_Libra.term0_0,JGs_Libra.term0_1,JGs_Libra.term0_2,JGs_Libra.term0_3]) 0#usize=ok JGs_Libra.term0_0 := by rfl
  have read1 : Array.index_usize (Array.make 4#usize [JGs_Libra.term0_0,JGs_Libra.term0_1,JGs_Libra.term0_2,JGs_Libra.term0_3]) 1#usize=ok JGs_Libra.term0_1 := by rfl
  have read2 : Array.index_usize (Array.make 4#usize [JGs_Libra.term0_0,JGs_Libra.term0_1,JGs_Libra.term0_2,JGs_Libra.term0_3]) 2#usize=ok JGs_Libra.term0_2 := by rfl
  have read3 : Array.index_usize (Array.make 4#usize [JGs_Libra.term0_0,JGs_Libra.term0_1,JGs_Libra.term0_2,JGs_Libra.term0_3]) 3#usize=ok JGs_Libra.term0_3 := by rfl
  unfold FJm_LibraStages.totals
  rw [read0,bind_tc_ok,read1,bind_tc_ok,sum0call2,bind_tc_ok,read2,bind_tc_ok,sum0call3,bind_tc_ok,read3,bind_tc_ok,sum0call4,bind_tc_ok]
#print axioms totals
theorem finish : FJm_LibraStages.finish 0#usize JGs_LibraScale0.value 1#usize sum0_2 sum0_3 sum0_4
    q0_4 q0_16 JGq_Powers1.a4 JGs_LibraEnd.initial {start:=1#usize,«end»:=2#usize}=
    ok (.cont ({start:=1#usize,«end»:=2#usize},JGs_LibraEnd.middle)) := by
  unfold FJm_LibraStages.finish
  simp only [ite_true]
  rw [call_a,bind_tc_ok,JGs_LibraWrites.up0,bind_tc_ok,call_b,bind_tc_ok,call_c,bind_tc_ok,JGs_LibraWrites.up1,bind_tc_ok]
#print axioms finish
end AspisR1.JGs_LibraStage0
end
