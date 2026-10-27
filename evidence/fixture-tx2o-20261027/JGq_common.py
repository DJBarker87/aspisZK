from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2]
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
def q(v):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(v)
a=x['nums']('JGo_TX2_WeightData','f02');b=x['nums']('JGo_TX2_WeightData','f03');cells=[x['qmul'](a[4*(i%4):4*(i%4)+4],b[4*(i//4):4*(i//4)+4]) for i in range(16)]
out={};mod='JGq_Common'
t='''import JGo_TX2_WeightData
import JGo_TX2_Range
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
abbrev Q := FIo_Install.NQ
def w := FIo_Install.toWeights JGo_TX2_WeightData.value
'''
for i,c in enumerate(cells):t+=f'def c{i} : Q := {q(c)}\n'
for i in range(17):t+=f'def a{i} : Array Q 16#usize := Array.make 16#usize ['+','.join(f'c{j}' if j<i else 'FIo_Native.aspis_core.field.QM31.ZERO' for j in range(16))+']\n'
out[mod+'Data']=t+'end AspisR1.JGq_Common\nend\n'
for i in range(16):
 out[mod+f'Step{i:02}']=f'''import {mod}Data
import FJf_CommonIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] FIo_Native.weights.Weights.pair_loop1
/-- One actual common-coefficient write, on the installed weight object. -/
theorem step{i} : FIo_Native.weights.Weights.pair_loop1.body w
    {{start:={i}#usize,«end»:=16#usize}} a{i}=
    ok (.cont ({{start:={i+1}#usize,«end»:=16#usize}},a{i+1})) := by
  have low : ({i}#usize &&& 3#usize)={i%4}#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.low];rfl)
  have high : Usize.wrapping_shr {i}#usize 2#u32={i//4}#usize :=
    UScalar.eq_of_val_eq (by rw [FJf_CommonIndices.high];rfl)
  unfold FIo_Native.weights.Weights.pair_loop1.body
  rw [JGo_TX2_Range.next {i}#usize 16#usize {i+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry,lift,bind_tc_ok,low,high]
  with_unfolding_all rfl
#print axioms step{i}
end AspisR1.JGq_Common
end
'''
t='\n'.join(f'import {mod}Step{i:02}' for i in range(16))+'''\nset_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
abbrev S := core.ops.range.Range Usize × Array Q 16#usize
def states : Nat → S
'''
for i in range(16):t+=f'  | {i} => ({{start:={i}#usize,«end»:=16#usize}},a{i})\n'
t+='''  | _ => ({start:=16#usize,«end»:=16#usize},a16)
theorem source : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
    w (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (w,a16) := by
  unfold FIo_Native.weights.Weights.pair_loop1
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.weights.Weights.pair_loop1.body w s.1 s.2) states 16 (w,a16)
  · intro i hi
    interval_cases i
'''
for i in range(16):t+=f'    · exact step{i}\n'
t+='''  · unfold FIo_Native.weights.Weights.pair_loop1.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_Common
end
''';out[mod]=t
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'shared coefficient stages')
