from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
P=2147483647;MASK=2**64-1
def fold(n):return (n&P)+(n>>31)
def raw(v,q):
 a,b,c,d=v;e,f,g,h=q;pp=P*P;u=fold((c*g+pp-d*h)&MASK);v=fold(c*h+d*g)
 return [(a*e+pp-b*f+2*u+3*P-v)&MASK,(a*f+b*e+u+2*v)&MASK,(a*g+c*e+2*pp-b*h-d*f)&MASK,(a*h+b*g+c*f+d*e)&MASK]
def q(v):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(v)
def dot(sums):return '⟨Array.make 4#usize ['+','.join(str(n)+'#u64' for n in sums)+']⟩'
def state(sums,count):return '⟨'+dot(sums[:4])+','+dot(sums[4:])+','+str(count)+'#usize⟩'
out={};s='''import JGq_SharedPartials
import JGq_Scale0
import JGq_Scale1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_High
open Aeneas Aeneas.Std Result ControlFlow
'''
parts=[x['nums']('JGq_PartialData',f'value{i}') for i in range(4)];high=[]
for tag in [0,2]:
 coeff=x['nums']('JGo_TX2_WeightData',f'f{tag}4');sums=[0]*8
 s+=f'def row{tag} := FIn_WeightsInstall.mapArray FIo_Install.toQ JGo_TX2_WeightData.f{tag}4\n'
 s+=f'def d{tag}_0 : FIo_Native.fast_pairing.EbyKDot := {state(sums,0)}\n'
 for j in range(4):
  c=coeff[4*j:4*j+4];s+=f'def c{tag}_{j} : FIo_Install.NQ := '+q(c)+'\n'
  raws=raw(parts[j][:4],c)+raw(parts[j][4:],c);sums=[(a+fold(b))&MASK for a,b in zip(sums,raws)]
  s+=f'def d{tag}_{j+1} : FIo_Native.fast_pairing.EbyKDot := {state(sums,j+1)}\n'
 high.append([z%P for z in sums]);s+=f'def high{tag} : FIo_Install.NE := '+x['wide'](high[-1])+'\n'
scale=x['mul'](x['nums']('JGq_Scale0','value'),x['nums']('JGq_Scale1','value'));s+='def scale : FIo_Install.NE := '+x['wide'](scale)+'\n'
for tag,h in zip([0,2],high):s+=f'def value{tag} : FIo_Install.NE := '+x['wide'](x['mul'](scale,h))+'\n'
out['JGq_HighData']=s+'end AspisR1.JGq_High\nend\n'
for tag in [0,2]:
 s='''import JGq_HighData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_High
open Aeneas Aeneas.Std Result ControlFlow
'''
 for j in range(4):
  s+=f'''theorem push{tag}_{j} : FIo_Native.fast_pairing.EbyKDot.push d{tag}_{j}
    JGq_Partial.value{j} c{tag}_{j}=ok (.Ok (),d{tag}_{j+1}) := by
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source]
  with_unfolding_all rfl
#print axioms push{tag}_{j}
'''
 s+=f'''theorem finish{tag} : FIo_Native.fast_pairing.EbyKDot.finish d{tag}_4=ok high{tag} := by with_unfolding_all rfl
#print axioms finish{tag}
'''
 for j in range(4):
  s+=f'''theorem step{tag}_{j} : FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row{tag}
    {{start:={j}#usize,«end»:=4#usize}} d{tag}_{j}=
    ok (.cont ({{start:={j+1}#usize,«end»:=4#usize}},d{tag}_{j+1})) := by
  have rp : Array.index_usize JGq_SharedPartials.value {j}#usize=ok JGq_Partial.value{j} := by rfl
  have rq : Array.index_usize row{tag} {j}#usize=ok c{tag}_{j} := by rfl
  unfold FIo_Native.weights.high_dot_loop.body
  rw [JGo_TX2_Range.next {j}#usize 4#usize {j+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [rp,bind_tc_ok,rq,bind_tc_ok,push{tag}_{j},bind_tc_ok]
  rfl
#print axioms step{tag}_{j}
'''
 s+=f'''abbrev S{tag} := core.ops.range.Range Usize × FIo_Native.fast_pairing.EbyKDot
def states{tag} : Nat → S{tag}
'''
 for j in range(4):s+=f'  | {j} => ({{start:={j}#usize,«end»:=4#usize}},d{tag}_{j})\n'
 s+=f'''  | _ => ({{start:=4#usize,«end»:=4#usize}},d{tag}_4)
theorem source{tag} : FIo_Native.weights.high_dot JGq_SharedPartials.value row{tag}=ok (.Ok high{tag}) := by
  have new : FIo_Native.fast_pairing.EbyKDot.new=ok d{tag}_0 := by rfl
  unfold FIo_Native.weights.high_dot
  rw [new,bind_tc_ok]
  unfold FIo_Native.weights.high_dot_loop
  apply JGo_TX2_LoopChain.source
    (fun x : S{tag}=>FIo_Native.weights.high_dot_loop.body JGq_SharedPartials.value row{tag} x.1 x.2)
    states{tag} 4 (.Ok high{tag})
  · intro i hi
    interval_cases i
'''
 for j in range(4):s+=f'    · exact step{tag}_{j}\n'
 s+=f'''  · unfold FIo_Native.weights.high_dot_loop.body
    have stop : core.iter.range.IteratorRange.next core.iter.range.StepUsize
        ({{start:=4#usize,«end»:=4#usize}} : core.ops.range.Range Usize)=ok (none,{{start:=4#usize,«end»:=4#usize}}) := by with_unfolding_all rfl
    rw [stop,bind_tc_ok]
    change (do
      let x ← FIo_Native.fast_pairing.EbyKDot.finish d{tag}_4
      ok (.done (.Ok x)))=_
    rw [finish{tag},bind_tc_ok]
#print axioms source{tag}
end AspisR1.JGq_High
end
''';out[f'JGq_High{tag}']=s
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'high dot stages')
