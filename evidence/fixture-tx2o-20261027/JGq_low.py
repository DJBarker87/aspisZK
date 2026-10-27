from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
P=2147483647;perm=[0,3,2,1];aps=[]
for tag in ['0','1']:
 alpha=x['scalar']('JFq_Alpha'+tag);v=[[1]+[0]*7]
 for _ in range(3):v.append(x['mul'](v[-1],alpha))
 aps.append(v)
cells=[];products=[]
for i in range(16):
 prod=x['mul'](aps[0][perm[i%4]],aps[1][perm[i//4]]);products.append(prod);cells.append([(a*pow(16,-1,P))%P for a in prod])
out={};t='''import JGq_Powers0
import JGq_Powers1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
abbrev E := FIo_Install.NE
'''
for i in range(16):t+=f'def product{i} : E := '+x['wide'](products[i])+f'\ndef c{i} : E := '+x['wide'](cells[i])+'\n'
for i in range(17):t+=f'def a{i} : Array E 16#usize := Array.make 16#usize ['+','.join(f'c{j}' if j<i else 'FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO' for j in range(16))+']\n'
out['JGq_LowData']=t+'end AspisR1.JGq_Low\nend\n'
for i in range(16):
 t=f'''import JGq_LowData
import JGq_LowTools
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
theorem multiply{i} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul
    JGq_Powers0.p{perm[i%4]} JGq_Powers1.p{perm[i//4]}=ok product{i} := by with_unfolding_all rfl
#print axioms multiply{i}
theorem scale{i} : FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product{i} 134217728#u32=ok c{i} := by with_unfolding_all rfl
#print axioms scale{i}
theorem step{i} : FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4
    {{start:={i}#usize,«end»:=16#usize}} a{i}=
    ok (.cont ({{start:={i+1}#usize,«end»:=16#usize}},a{i+1})) := by
  apply JGq_LowTools.step JGq_Powers0.a4 JGq_Powers1.a4
    {{start:={i}#usize,«end»:=16#usize}} {{start:={i+1}#usize,«end»:=16#usize}}
    a{i} a{i+1} {i}#usize {i%4}#usize {i//4}#usize {perm[i%4]}#usize {perm[i//4]}#usize
    JGq_Powers0.p{perm[i%4]} JGq_Powers1.p{perm[i//4]} product{i} c{i} 134217728#u32
  · exact JGo_TX2_Range.next {i}#usize 16#usize {i+1}#usize (by decide) (by decide)
  · rfl
  · with_unfolding_all rfl
  · rfl
  · rfl
  · with_unfolding_all rfl
  · rfl
  · exact multiply{i}
  · with_unfolding_all rfl
  · exact scale{i}
  · rfl
#print axioms step{i}
end AspisR1.JGq_Low
end
''';out[f'JGq_LowStep{i:02}']=t
for b in range(4):
 text='import JGq_LowData\nimport JGq_LowTools\n'+''.join(out[f'JGq_LowStep{i:02}'].split('import JGq_LowTools\n',1)[1] for i in range(4*b,4*b+4))
 out[f'JGq_LowGroup{b}']=text
for i in range(16):del out[f'JGq_LowStep{i:02}']
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'low coefficient stages')
