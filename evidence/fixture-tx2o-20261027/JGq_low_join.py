from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2]
s='\n'.join(f'import JGq_LowGroup{i}' for i in range(4))+'''
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
abbrev S := core.ops.range.Range Usize × Array E 16#usize
def states : Nat → S
'''
for i in range(16):s+=f'  | {i} => ({{start:={i}#usize,«end»:=16#usize}},a{i})\n'
s+='''  | _ => ({start:=16#usize,«end»:=16#usize},a16)
theorem source : FIo_Native.weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize}
    JGq_Powers0.a4 JGq_Powers1.a4 (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok a16 := by
  unfold FIo_Native.weights.Weights.pair_loop7
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4 s.1 s.2)
    states 16 a16
  · intro i hi
    interval_cases i
'''
for i in range(16):s+=f'    · exact step{i}\n'
s+='''  · unfold FIo_Native.weights.Weights.pair_loop7.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_Low
end
'''
p=R/'lean/JGq_Low.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
