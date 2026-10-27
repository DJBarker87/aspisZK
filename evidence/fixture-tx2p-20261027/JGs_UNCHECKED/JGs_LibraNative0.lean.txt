import JGs_LibraPowers0
import JGs_LibraTerms0
import JGs_LibraWrites
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraNative
open Aeneas Aeneas.Std Result ControlFlow
open JGs_Libra JGs_LibraEnd
theorem step0 : FIo_Native.weights.factored_s2_libra_weights_loop.body JGq_Powers0.a4 JGq_Powers1.a4
    (FIo_Install.toWeights JGo_TX2_WeightData.value).extra {start:=0#usize,«end»:=2#usize} initial=
    ok (.cont ({start:=1#usize,«end»:=2#usize},middle)) := by
  unfold FIo_Native.weights.factored_s2_libra_weights_loop.body
  rw [JGo_TX2_Range.next 0#usize 2#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [extra0,bind_tc_ok,power0_0,bind_tc_ok,power0_1,bind_tc_ok,power0_2,bind_tc_ok,power0_3,bind_tc_ok]
  have read2 : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_1,q0_2,q0_3]) 2#usize=ok q0_2 := by rfl
  rw [read2,bind_tc_ok,power0_4,bind_tc_ok,power0_5,bind_tc_ok,power0_6,bind_tc_ok,power0_7,bind_tc_ok]
  have low : FIo_Native.weights.Weights.scalar_factor (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_1,q0_2,q0_3]) JGq_Powers0.a4=ok JGs_LibraScale0.value := by
    with_unfolding_all exact JGs_LibraScale0.source
  rw [low,bind_tc_ok]
  have perm0 : Array.index_usize FIo_Native.weights.PERM 0#usize=ok 0#usize := by with_unfolding_all rfl
  have ap0 : Array.index_usize JGq_Powers1.a4 0#usize=ok JGq_Powers1.p0 := by rfl
  have qp0 : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_4,q0_8,q0_12]) 0#usize=ok q0_0 := by with_unfolding_all rfl
  rw [perm0,bind_tc_ok,ap0,bind_tc_ok,qp0,bind_tc_ok,mixed0_0,bind_tc_ok,quarter0_0,bind_tc_ok]
  have perm1 : Array.index_usize FIo_Native.weights.PERM 1#usize=ok 3#usize := by with_unfolding_all rfl
  have ap1 : Array.index_usize JGq_Powers1.a4 3#usize=ok JGq_Powers1.p3 := by rfl
  have qp1 : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_4,q0_8,q0_12]) 1#usize=ok q0_4 := by with_unfolding_all rfl
  rw [perm1,bind_tc_ok,ap1,bind_tc_ok,qp1,bind_tc_ok,mixed0_1,bind_tc_ok,quarter0_1,bind_tc_ok]
  have perm2 : Array.index_usize FIo_Native.weights.PERM 2#usize=ok 2#usize := by with_unfolding_all rfl
  have ap2 : Array.index_usize JGq_Powers1.a4 2#usize=ok JGq_Powers1.p2 := by rfl
  have qp2 : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_4,q0_8,q0_12]) 2#usize=ok q0_8 := by with_unfolding_all rfl
  rw [perm2,bind_tc_ok,ap2,bind_tc_ok,qp2,bind_tc_ok,mixed0_2,bind_tc_ok,quarter0_2,bind_tc_ok]
  have perm3 : Array.index_usize FIo_Native.weights.PERM 3#usize=ok 1#usize := by with_unfolding_all rfl
  have ap3 : Array.index_usize JGq_Powers1.a4 1#usize=ok JGq_Powers1.p1 := by rfl
  have qp3 : Array.index_usize (Array.make 4#usize [FIo_Native.aspis_core.field.QM31.ONE,q0_4,q0_8,q0_12]) 3#usize=ok q0_12 := by with_unfolding_all rfl
  rw [perm3,bind_tc_ok,ap3,bind_tc_ok,qp3,bind_tc_ok,mixed0_3,bind_tc_ok,quarter0_3,bind_tc_ok]
  have tr0 : Array.index_usize (Array.make 4#usize [term0_0,term0_1,term0_2,term0_3]) 0#usize=ok term0_0 := by rfl
  have tr1 : Array.index_usize (Array.make 4#usize [term0_0,term0_1,term0_2,term0_3]) 1#usize=ok term0_1 := by rfl
  have tr2 : Array.index_usize (Array.make 4#usize [term0_0,term0_1,term0_2,term0_3]) 2#usize=ok term0_2 := by rfl
  have tr3 : Array.index_usize (Array.make 4#usize [term0_0,term0_1,term0_2,term0_3]) 3#usize=ok term0_3 := by rfl
  rw [tr0,bind_tc_ok,tr1,bind_tc_ok,sum0call2,bind_tc_ok,tr2,bind_tc_ok,sum0call3,bind_tc_ok,tr3,bind_tc_ok,sum0call4,bind_tc_ok]
  simp only [ite_true]
  rw [call_a,bind_tc_ok,JGs_LibraWrites.up0,bind_tc_ok,call_b,bind_tc_ok,call_c,bind_tc_ok,JGs_LibraWrites.up1,bind_tc_ok]
#print axioms step0
end AspisR1.JGs_LibraNative
end
