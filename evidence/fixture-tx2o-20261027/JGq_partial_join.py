from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];out={}
for s in range(4):
 t='\n'.join(f'import JGq_PartialPush{s}_{b}' for b in range(4))+f'''
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
theorem finish{s} : FIo_Native.fast_pairing.EbyKDot.finish d{s}_16=ok value{s} := by with_unfolding_all rfl
#print axioms finish{s}
'''
 for j in range(16):
  i=16*s+j;owner=f'JGo_TX2_Message{(i//8)*8:02}'
  t+=f'''theorem step{s}_{j} : FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 {s}#usize
    {{start:={j}#usize,«end»:=16#usize}} d{s}_{j}=
    ok (.cont ({{start:={j+1}#usize,«end»:=16#usize}},d{s}_{j+1})) := by
  have mul : Usize.wrapping_mul 16#usize {s}#usize={16*s}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_mul_value 16#usize {s}#usize (by decide))
  have add : Usize.wrapping_add {16*s}#usize {j}#usize={i}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value {16*s}#usize {j}#usize (by decide))
  have read : Array.index_usize JGq_Common.a16 {j}#usize=ok JGq_Common.c{j} := by rfl
  unfold FIo_Native.weights.partial_dot_loop.body
  rw [JGo_TX2_Range.next {j}#usize 16#usize {j+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,mul,add]
  rw [show FIo_Native.weights.field f {i}#usize=ok (FIo_Install.toE {owner}.value{i:02}) from {owner}.native_field{i:02},bind_tc_ok,
    read,bind_tc_ok,push{s}_{j},bind_tc_ok]
  rfl
#print axioms step{s}_{j}
'''
 t+=f'''abbrev S{s} := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states{s} : Nat → S{s}
'''
 for j in range(16):t+=f'  | {j} => ({{start:={j}#usize,«end»:=16#usize}},d{s}_{j})\n'
 t+=f'''  | _ => ({{start:=16#usize,«end»:=16#usize}},d{s}_16)
theorem source{s} : FIo_Native.weights.partial_dot f JGq_Common.a16 {s}#usize=ok (.Ok value{s}) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d{s}_0 := by rfl
  unfold FIo_Native.weights.partial_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.partial_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S{s}=>FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 {s}#usize x.1 x.2)
    states{s} 16 (.Ok value{s})
  · intro i hi
    interval_cases i
'''
 for j in range(16):t+=f'    · exact step{s}_{j}\n'
 t+=f'''  · change FIo_Native.weights.partial_dot_loop.body f JGq_Common.a16 {s}#usize
        {{start:=16#usize,«end»:=16#usize}} d{s}_16=ok (.done (.Ok value{s}))
    unfold FIo_Native.weights.partial_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({{start:=16#usize,«end»:=16#usize}} : core.ops.range.Range Usize)=ok (none,{{start:=16#usize,«end»:=16#usize}}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    simp only [Aeneas.Std.uncurry]
    rw [finish{s},bind_tc_ok]
#print axioms source{s}
end AspisR1.JGq_Partial
end
''';out[f'JGq_Partial{s}']=t
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'native partial-dot joins')
