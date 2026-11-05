import NIG_Indices
import NHI_ForwardRange
set_option autoImplicit false
namespace NIG_Geometry
open Aeneas Aeneas.Std Result ControlFlow
abbrev Range:=core.ops.range.Range Usize

theorem shift1024 : Usize.wrapping_shr 1024#usize 2#u32=256#usize := by
 apply UScalar.eq_of_val_eq
 rw [NIG_Indices.shift_two]
 rfl

theorem shift256 : Usize.wrapping_shr 256#usize 2#u32=64#usize := by
 apply UScalar.eq_of_val_eq
 rw [NIG_Indices.shift_two]
 rfl

theorem expected : FIo_Native.weights.Weights.pair_loop0
 {start:=0#usize,«end»:=2#usize} 1024#usize=ok 64#usize := by
 have first:NHI_ForwardRange.next ({start:=0#usize,«end»:=2#usize}:Range)=
  ok (some 0#usize,({start:=1#usize,«end»:=2#usize}:Range)):=
  NHI_ForwardRange.exact_step _ 1#usize (by decide) (by decide)
 have second:NHI_ForwardRange.next ({start:=1#usize,«end»:=2#usize}:Range)=
  ok (some 1#usize,({start:=2#usize,«end»:=2#usize}:Range)):=
  NHI_ForwardRange.exact_step _ 2#usize (by decide) (by decide)
 have last:=NHI_ForwardRange.done ({start:=2#usize,«end»:=2#usize}:Range) (by decide)
 unfold NHI_ForwardRange.next at first second last
 unfold FIo_Native.weights.Weights.pair_loop0
 rw [loop.eq_def]
 simp only [FIo_Native.weights.Weights.pair_loop0.body,first,shift1024,lift,bind_tc_ok]
 rw [loop.eq_def]
 simp only [FIo_Native.weights.Weights.pair_loop0.body,second,shift256,lift,bind_tc_ok]
 rw [loop.eq_def]
 simp only [FIo_Native.weights.Weights.pair_loop0.body,last,bind_tc_ok]
 rfl

#print axioms shift1024
#print axioms shift256
#print axioms expected
end NIG_Geometry
