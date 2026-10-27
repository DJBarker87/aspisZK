import JGo_TX2_WeightData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightRow0
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step0 : weights_new_loop0_loop0.body points 0#usize
    {start:=0#usize,«end»:=5#usize} factors00=
      ok (.cont ({start:=1#usize,«end»:=5#usize},factors01)) := by
  with_unfolding_all rfl
#print axioms step0
theorem step1 : weights_new_loop0_loop0.body points 0#usize
    {start:=1#usize,«end»:=5#usize} factors01=
      ok (.cont ({start:=2#usize,«end»:=5#usize},factors02)) := by
  with_unfolding_all rfl
#print axioms step1
theorem step2 : weights_new_loop0_loop0.body points 0#usize
    {start:=2#usize,«end»:=5#usize} factors02=
      ok (.cont ({start:=3#usize,«end»:=5#usize},factors03)) := by
  with_unfolding_all rfl
#print axioms step2
theorem step3 : weights_new_loop0_loop0.body points 0#usize
    {start:=3#usize,«end»:=5#usize} factors03=
      ok (.cont ({start:=4#usize,«end»:=5#usize},factors04)) := by
  with_unfolding_all rfl
#print axioms step3
theorem step4 : weights_new_loop0_loop0.body points 0#usize
    {start:=4#usize,«end»:=5#usize} factors04=
      ok (.cont ({start:=5#usize,«end»:=5#usize},factors05)) := by
  with_unfolding_all rfl
#print axioms step4
end AspisR1.JGo_TX2_WeightRow0
end
