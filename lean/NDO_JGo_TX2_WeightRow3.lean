import NDO_JGo_TX2_WeightData
import RPu_FJf_Coordinates
import JGo_TX2_Range
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightRow3
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem product : field.QM31.mul z0x z0y=ok z0product := by with_unfolding_all rfl
#print axioms product
theorem double : FIn_WeightsExtract.double z0x=ok x0_1 := by with_unfolding_all rfl
#print axioms double
theorem step1 : weights_new_loop1_loop0.body 0#usize
    {start:=1#usize,«end»:=5#usize} factors16 x0_1=
      ok (.cont ({start:=2#usize,«end»:=5#usize},factors17,x0_2)) := by
  have index : Usize.wrapping_add 3#usize 0#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  unfold weights_new_loop1_loop0.body
  rw [JGo_TX2_Range.next 1#usize 5#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  simp only [lift,bind_tc_ok,index]
  with_unfolding_all rfl
#print axioms step1
theorem step2 : weights_new_loop1_loop0.body 0#usize
    {start:=2#usize,«end»:=5#usize} factors17 x0_2=
      ok (.cont ({start:=3#usize,«end»:=5#usize},factors18,x0_3)) := by
  have index : Usize.wrapping_add 3#usize 0#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  unfold weights_new_loop1_loop0.body
  rw [JGo_TX2_Range.next 2#usize 5#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  simp only [lift,bind_tc_ok,index]
  with_unfolding_all rfl
#print axioms step2
theorem step3 : weights_new_loop1_loop0.body 0#usize
    {start:=3#usize,«end»:=5#usize} factors18 x0_3=
      ok (.cont ({start:=4#usize,«end»:=5#usize},factors19,x0_4)) := by
  have index : Usize.wrapping_add 3#usize 0#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  unfold weights_new_loop1_loop0.body
  rw [JGo_TX2_Range.next 3#usize 5#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  simp only [lift,bind_tc_ok,index]
  with_unfolding_all rfl
#print axioms step3
theorem step4 : weights_new_loop1_loop0.body 0#usize
    {start:=4#usize,«end»:=5#usize} factors19 x0_4=
      ok (.cont ({start:=5#usize,«end»:=5#usize},factors20,x0_5)) := by
  have index : Usize.wrapping_add 3#usize 0#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  unfold weights_new_loop1_loop0.body
  rw [JGo_TX2_Range.next 4#usize 5#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  simp only [lift,bind_tc_ok,index]
  with_unfolding_all rfl
#print axioms step4
end AspisR1.JGo_TX2_WeightRow3
end
