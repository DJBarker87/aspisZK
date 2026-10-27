from pathlib import Path
import re,sys,json
R=Path(__file__).resolve().parents[2];P=2147483647;MASK=2**64-1
x={'__file__':str(R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py')};exec((R/'evidence/fixture-tx2n-20261027/JGo_arithmetic.py').read_text().split('mods,results=generate()')[0],x)
a=x['nums']('JGo_TX2_WeightData','f02');b=x['nums']('JGo_TX2_WeightData','f03');common=[x['qmul'](a[4*(i%4):4*(i%4)+4],b[4*(i//4):4*(i//4)+4]) for i in range(16)]
def fold(n):return (n&P)+(n>>31)
def raw(v,q):
 a,b,c,d=v;e,f,g,h=q;pp=P*P
 u=fold((c*g+pp-d*h)&MASK);v=fold(c*h+d*g)
 return [(a*e+pp-b*f+2*u+3*P-v)&MASK,(a*f+b*e+u+2*v)&MASK,(a*g+c*e+2*pp-b*h-d*f)&MASK,(a*h+b*g+c*f+d*e)&MASK]
def dot(sums):return '⟨Array.make 4#usize ['+','.join(str(n)+'#u64' for n in sums)+']⟩'
def state(sums,count):return '⟨'+dot(sums[:4])+','+dot(sums[4:])+','+str(count)+'#usize⟩'
values=[]
for i in range(64):
 mod=f'JGo_TX2_Message{(i//8)*8:02}';values.append(x['nums'](mod,f'value{i:02}'))
for i in range(64):
 for half in range(2):assert [z%P for z in raw(values[i][4*half:4*half+4],common[i%16])]==x['qmul'](values[i][4*half:4*half+4],common[i%16])
out={};t='''import JGq_Common
import JGo_TX2_Message00
import JGo_TX2_Message08
import JGo_TX2_Message16
import JGo_TX2_Message24
import JGo_TX2_Message32
import JGo_TX2_Message40
import JGo_TX2_Message48
import JGo_TX2_Message56
import JGq_DotLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
def f := JFw_Frames.window 8007 2048
'''
for s in range(4):
 sums=[0]*8;t+=f'def d{s}_0 : FIo_Native.fast_pairing.EbyKDot := {state(sums,0)}\n'
 for j in range(16):
  raws=raw(values[16*s+j][:4],common[j])+raw(values[16*s+j][4:],common[j]);sums=[(old+fold(r))&MASK for old,r in zip(sums,raws)]
  t+=f'def d{s}_{j+1} : FIo_Native.fast_pairing.EbyKDot := {state(sums,j+1)}\n'
 t+=f'def value{s} : FIo_Install.NE := '+x['wide']([z%P for z in sums])+'\n'
out['JGq_PartialData']=t+'end AspisR1.JGq_Partial\nend\n'
for s in range(4):
 for block in range(4):
  t='''import JGq_PartialData
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Partial
open Aeneas Aeneas.Std Result ControlFlow
attribute [local irreducible] JFw_Frames.window
'''
  for j in range(4*block,4*block+4):
   i=16*s+j;owner=f'JGo_TX2_Message{(i//8)*8:02}';v=f'FIo_Install.toE {owner}.value{i:02}'
   t+=f'''theorem push{s}_{j} : FIo_Native.fast_pairing.EbyKDot.push d{s}_{j}
    ({v}) JGq_Common.c{j}=ok (.Ok (),d{s}_{j+1}) := by
  have inc : Usize.wrapping_add d{s}_{j}.count 1#usize={j+1}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value d{s}_{j}.count 1#usize (by decide))
  simp only [FIo_Native.fast_pairing.EbyKDot.push,
    FIo_Native.fast_pairing.canonical.Dot.push,JGq_DotLoop.source,inc]
  with_unfolding_all rfl
#print axioms push{s}_{j}
'''
  out[f'JGq_PartialPush{s}_{block}']=t+'end AspisR1.JGq_Partial\nend\n'
for mod,t in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert p.read_text()==t
 else:p.write_text(t)
print(len(out),'partial-dot source stages')
