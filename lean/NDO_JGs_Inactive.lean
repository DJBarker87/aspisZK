import NDO_JGs_InactiveCoefficients
import NDO_JGs_InactiveW0
import NDO_JGs_InactiveW1
import NDO_JGs_InactiveW2
import NDO_JGs_InactiveW3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Inactive
open Aeneas Aeneas.Std Result ControlFlow
theorem group0 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=0#usize,«end»:=12#usize} pair0=ok (.cont ({start:=1#usize,«end»:=12#usize},pair1)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 0#usize 12#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight0,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group0
theorem group1 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=1#usize,«end»:=12#usize} pair1=ok (.cont ({start:=2#usize,«end»:=12#usize},pair2)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 1#usize 12#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight1,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group1
theorem group2 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=2#usize,«end»:=12#usize} pair2=ok (.cont ({start:=3#usize,«end»:=12#usize},pair3)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 2#usize 12#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight2,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group2
theorem group3 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=3#usize,«end»:=12#usize} pair3=ok (.cont ({start:=4#usize,«end»:=12#usize},pair4)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 3#usize 12#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight3,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group3
theorem group4 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=4#usize,«end»:=12#usize} pair4=ok (.cont ({start:=5#usize,«end»:=12#usize},pair5)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 4#usize 12#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight4,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group4
theorem group5 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=5#usize,«end»:=12#usize} pair5=ok (.cont ({start:=6#usize,«end»:=12#usize},pair6)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 5#usize 12#usize 6#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight5,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group5
theorem group6 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=6#usize,«end»:=12#usize} pair6=ok (.cont ({start:=7#usize,«end»:=12#usize},pair7)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 6#usize 12#usize 7#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight6,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group6
theorem group7 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=7#usize,«end»:=12#usize} pair7=ok (.cont ({start:=8#usize,«end»:=12#usize},pair8)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 7#usize 12#usize 8#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight7,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group7
theorem group8 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=8#usize,«end»:=12#usize} pair8=ok (.cont ({start:=9#usize,«end»:=12#usize},pair9)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 8#usize 12#usize 9#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight8,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group8
theorem group9 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=9#usize,«end»:=12#usize} pair9=ok (.cont ({start:=10#usize,«end»:=12#usize},pair10)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 9#usize 12#usize 10#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight9,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group9
theorem group10 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=10#usize,«end»:=12#usize} pair10=ok (.cont ({start:=11#usize,«end»:=12#usize},pair11)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 10#usize 12#usize 11#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight10,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group10
theorem group11 : FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64
    {start:=11#usize,«end»:=12#usize} pair11=ok (.cont ({start:=12#usize,«end»:=12#usize},pair12)) := by
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
  rw [JGo_TX2_Range.next 11#usize 12#usize 12#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [weight11,bind_tc_ok]
  with_unfolding_all rfl
#print axioms group11
def pairStates : Nat → core.ops.range.Range Usize × E
  | 0 => ({start:=0#usize,«end»:=12#usize},pair0)
  | 1 => ({start:=1#usize,«end»:=12#usize},pair1)
  | 2 => ({start:=2#usize,«end»:=12#usize},pair2)
  | 3 => ({start:=3#usize,«end»:=12#usize},pair3)
  | 4 => ({start:=4#usize,«end»:=12#usize},pair4)
  | 5 => ({start:=5#usize,«end»:=12#usize},pair5)
  | 6 => ({start:=6#usize,«end»:=12#usize},pair6)
  | 7 => ({start:=7#usize,«end»:=12#usize},pair7)
  | 8 => ({start:=8#usize,«end»:=12#usize},pair8)
  | 9 => ({start:=9#usize,«end»:=12#usize},pair9)
  | 10 => ({start:=10#usize,«end»:=12#usize},pair10)
  | 11 => ({start:=11#usize,«end»:=12#usize},pair11)
  | _ => ({start:=12#usize,«end»:=12#usize},pair12)
theorem paired : FIo_Native.weights.s2_grouped_inactive_pair_loop1 {start:=0#usize,«end»:=12#usize} JGq_Low.a16 cs64
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok pair12 := by
  have initial : FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=pair0 := by with_unfolding_all rfl
  rw [initial]
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1
  apply JGo_TX2_LoopChain.source
    (fun t : core.ops.range.Range Usize × E=>FIo_Native.weights.s2_grouped_inactive_pair_loop1.body JGq_Low.a16 cs64 t.1 t.2) pairStates 12 pair12
  · intro i hi
    interval_cases i
    · exact group0
    · exact group1
    · exact group2
    · exact group3
    · exact group4
    · exact group5
    · exact group6
    · exact group7
    · exact group8
    · exact group9
    · exact group10
    · exact group11
  · unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1.body
    with_unfolding_all rfl
#print axioms paired
theorem source : FIo_Native.weights.grouped_inactive_pair JGq_PairShape.w JGq_PairShape.f JGq_Low.a16=ok pair12 := by
  have variant : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq JGq_PairShape.w.variant .S2=ok true := by
    change FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true
    unfold FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.read_discriminant
    simp only [eq_self,decide_true]
  have width : Usize.wrapping_mul 64#usize 32#usize=2048#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 64#usize 32#usize (by decide))
  unfold FIo_Native.weights.grouped_inactive_pair
  rw [variant,bind_tc_ok]
  simp only [ite_true,eq_self,JGq_PairShape.length,lift,bind_tc_ok,width]
  unfold FIo_Native.weights.s2_grouped_inactive_pair
  simp only [coefficients,bind_tc_ok,paired]
#print axioms source
end AspisR1.JGs_Inactive
end
