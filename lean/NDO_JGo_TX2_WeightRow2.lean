import NDO_JGo_TX2_WeightData
import RPu_FJf_Coordinates
import JGo_TX2_Range
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightRow2
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
theorem step0 : weights_new_loop0_loop0.body points 2#usize
    {start:=0#usize,«end»:=5#usize} factors10=
      ok (.cont ({start:=1#usize,«end»:=5#usize},factors11)) := by
  have ix := FJf_Coordinates.indices 3#usize (by decide)
  have ix9 : Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize 3#usize)=3#usize :=
    UScalar.eq_of_val_eq ix.1
  have ix8 : Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize 3#usize)=2#usize :=
    UScalar.eq_of_val_eq ix.2
  unfold weights_new_loop0_loop0.body
  rw [JGo_TX2_Range.next 0#usize 5#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show Array.index_usize TAU 0#usize=ok 3#usize from by unfold TAU;rfl,bind_tc_ok]
  simp only [lift,bind_tc_ok,ix9,ix8]
  with_unfolding_all rfl
#print axioms step0
theorem step1 : weights_new_loop0_loop0.body points 2#usize
    {start:=1#usize,«end»:=5#usize} factors11=
      ok (.cont ({start:=2#usize,«end»:=5#usize},factors12)) := by
  have ix := FJf_Coordinates.indices 4#usize (by decide)
  have ix9 : Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize 4#usize)=1#usize :=
    UScalar.eq_of_val_eq ix.1
  have ix8 : Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize 4#usize)=0#usize :=
    UScalar.eq_of_val_eq ix.2
  unfold weights_new_loop0_loop0.body
  rw [JGo_TX2_Range.next 1#usize 5#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show Array.index_usize TAU 1#usize=ok 4#usize from by unfold TAU;rfl,bind_tc_ok]
  simp only [lift,bind_tc_ok,ix9,ix8]
  with_unfolding_all rfl
#print axioms step1
theorem step2 : weights_new_loop0_loop0.body points 2#usize
    {start:=2#usize,«end»:=5#usize} factors12=
      ok (.cont ({start:=3#usize,«end»:=5#usize},factors13)) := by
  have ix := FJf_Coordinates.indices 2#usize (by decide)
  have ix9 : Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize 2#usize)=5#usize :=
    UScalar.eq_of_val_eq ix.1
  have ix8 : Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize 2#usize)=4#usize :=
    UScalar.eq_of_val_eq ix.2
  unfold weights_new_loop0_loop0.body
  rw [JGo_TX2_Range.next 2#usize 5#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show Array.index_usize TAU 2#usize=ok 2#usize from by unfold TAU;rfl,bind_tc_ok]
  simp only [lift,bind_tc_ok,ix9,ix8]
  with_unfolding_all rfl
#print axioms step2
theorem step3 : weights_new_loop0_loop0.body points 2#usize
    {start:=3#usize,«end»:=5#usize} factors13=
      ok (.cont ({start:=4#usize,«end»:=5#usize},factors14)) := by
  have ix := FJf_Coordinates.indices 0#usize (by decide)
  have ix9 : Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize 0#usize)=9#usize :=
    UScalar.eq_of_val_eq ix.1
  have ix8 : Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize 0#usize)=8#usize :=
    UScalar.eq_of_val_eq ix.2
  unfold weights_new_loop0_loop0.body
  rw [JGo_TX2_Range.next 3#usize 5#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show Array.index_usize TAU 3#usize=ok 0#usize from by unfold TAU;rfl,bind_tc_ok]
  simp only [lift,bind_tc_ok,ix9,ix8]
  with_unfolding_all rfl
#print axioms step3
theorem step4 : weights_new_loop0_loop0.body points 2#usize
    {start:=4#usize,«end»:=5#usize} factors14=
      ok (.cont ({start:=5#usize,«end»:=5#usize},factors15)) := by
  have ix := FJf_Coordinates.indices 1#usize (by decide)
  have ix9 : Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize 1#usize)=7#usize :=
    UScalar.eq_of_val_eq ix.1
  have ix8 : Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize 1#usize)=6#usize :=
    UScalar.eq_of_val_eq ix.2
  unfold weights_new_loop0_loop0.body
  rw [JGo_TX2_Range.next 4#usize 5#usize 5#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show Array.index_usize TAU 4#usize=ok 1#usize from by unfold TAU;rfl,bind_tc_ok]
  simp only [lift,bind_tc_ok,ix9,ix8]
  with_unfolding_all rfl
#print axioms step4
end AspisR1.JGo_TX2_WeightRow2
end
