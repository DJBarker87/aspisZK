from pathlib import Path
import re,sys,runpy
P=Path(__file__).resolve().parent;R=P.parents[1]
x=runpy.run_path(str(P/'JGo_arithmetic.py'));prime=x['P'];mul=x['qmul'];add=x['add']
zero=[0]*4;one=[1,0,0,0]
def sub(a,b):return [(u-v)%prime for u,v in zip(a,b)]
def q(v):return '⟨⟨%s#u32,%s#u32⟩,⟨%s#u32,%s#u32⟩⟩'%tuple(v)
def arr(xs,n=None):return f'Array.make {n or len(xs)}#usize ['+','.join(xs)+']'
def scalar4(mod):
 t=(R/f'lean/{mod}.lean').read_text();return list(map(int,re.findall(r'(\d+)#u32',re.search('def decoded[^\n]*:= (.*)',t).group(1))))
a=[scalar4(f'JFq_Sem{i:02}') for i in range(10)]
z=[scalar4(f'JFq_Z{i}') for i in range(4)]
head='''import FIo_Install
import JFo_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightData
open Aeneas Aeneas.Std Result FIn_WeightsExtract
abbrev Q := field.QM31
abbrev Row := Array (Array Q 4#usize) 5#usize
abbrev Factors := Array Row 5#usize
'''
s=head+f'def alpha : Array Q 10#usize := {arr([q(v) for v in a])}\n'
s+='theorem alpha_pin : FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ JFo_Prepared.value.semantic_alpha=alpha := by rfl\n#print axioms alpha_pin\n'
s+='def z : Array circle.SecureCirclePoint 2#usize := '+arr(['⟨'+q(z[0])+','+q(z[1])+'⟩','⟨'+q(z[2])+','+q(z[3])+'⟩'])+'\n'
s+='theorem z_pin : FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint JFo_Prepared.value.z=z := by rfl\n#print axioms z_pin\n'
succ=[u[:] for u in a];carry=one[:]
for step in range(11):
 s+=f'def successor{step:02} : Array Q 10#usize := '+arr([q(v) for v in succ])+'\n'
 s+=f'def carry{step:02} : Q := '+q(carry)+'\n'
 if step<10:
  i=9-step;t=mul(a[i],carry);succ[i]=sub(add(a[i],carry),add(t,t));carry=t
absorb=[u[:] for u in a];absorb[7]=sub(one,absorb[7]);absorb[6]=sub(one,absorb[6])
s+='def absorption : Array Q 10#usize := '+arr([q(v) for v in absorb])+'\n'
s+='def points : Array (Array Q 10#usize) 3#usize := Array.make 3#usize [alpha,successor10,absorption]\n'
points=[a,succ,absorb];tau=[3,4,2,0,1]
factors=[[[0]*4 for _ in range(4)] for _ in range(25)]
for k in range(3):
 for d in range(5):
  u=points[k][9-2*tau[d]];v=points[k][8-2*tau[d]]
  factors[5*k+d]=[mul(sub(one,u),sub(one,v)),mul(u,sub(one,v)),mul(sub(one,u),v),mul(u,v)]
for k in range(2):
 u,v=z[2*k:2*k+2];factors[15+5*k]=[one,v,u,mul(u,v)];u=sub(add(mul(u,u),mul(u,u)),one)
 for d in range(1,5):
  v=sub(add(mul(u,u),mul(u,u)),one);factors[15+5*k+d]=[one,u,v,mul(u,v)];u=sub(add(mul(v,v),mul(v,v)),one)
for k in range(5):
 for d in range(5):s+=f'def f{k}{d} : Array Q 4#usize := '+arr([q(v) for v in factors[5*k+d]])+'\n'
 for d in range(6):s+=f'def r{k}_{d} : Row := '+arr([f'f{k}{j}' if j<d else '(Array.repeat 4#usize field.QM31.ZERO)' for j in range(5)])+'\n'
for n in range(26):
 k,d=divmod(n,5)
 s+=f'def factors{n:02} : Factors := '+arr([f'r{j}_5' if j<k else f'r{j}_{d}' if j==k else f'r{j}_0' for j in range(5)])+'\n'
for k in range(2):
 u,v=z[2*k:2*k+2];t=mul(u,v)
 s+=f'def z{k}x : Q := '+q(u)+'\n'+f'def z{k}y : Q := '+q(v)+'\n'+f'def z{k}product : Q := '+q(t)+'\n'
 u=sub(add(mul(u,u),mul(u,u)),one)
 for d in range(1,6):
  s+=f'def x{k}_{d} : Q := '+q(u)+'\n'
  y=sub(add(mul(u,u),mul(u,u)),one);u=sub(add(mul(y,y),mul(y,y)),one)
s+='def value : Weights := ⟨.S2,factors25,points,Array.make 2#usize [alpha.val[8],alpha.val[9]]⟩\n'
s+='end AspisR1.JGo_TX2_WeightData\nend\n'
mods={'JGo_TX2_WeightData.lean':s}
for block in range(5):
 s='''import JGo_TX2_WeightData
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints'''+str(block)+'''
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
'''
 for step in range(2*block,2*block+2):
  s+=f'''theorem step{step:02} : state_only_prefix.state_only_statement_points_loop.body alpha
    ⟨{{start:=0#usize,«end»:={10-step}#usize}}⟩ successor{step:02} carry{step:02}=
      ok (.cont (⟨{{start:=0#usize,«end»:={9-step}#usize}}⟩,successor{step+1:02},carry{step+1:02})) := by
  with_unfolding_all rfl
#print axioms step{step:02}
'''
 s+=f'end AspisR1.JGo_TX2_WeightPoints{block}\nend\n';mods[f'JGo_TX2_WeightPoints{block}.lean']=s
# Factor row bodies only, all small named calls; joins follow after focused checks.
for k in range(5):
 s='''import JGo_TX2_WeightData
import FJf_Coordinates
import JGo_TX2_Range
import Port3_Wrapping
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightRow'''+str(k)+'''
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
'''
 if k<3:
  for d in range(5):
   n=k*5+d
   s+=f'''theorem step{d} : weights_new_loop0_loop0.body points {k}#usize
    {{start:={d}#usize,«end»:=5#usize}} factors{n:02}=
      ok (.cont ({{start:={d+1}#usize,«end»:=5#usize}},factors{n+1:02})) := by
  have ix := FJf_Coordinates.indices {tau[d]}#usize (by decide)
  have ix9 : Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize {tau[d]}#usize)={9-2*tau[d]}#usize :=
    UScalar.eq_of_val_eq ix.1
  have ix8 : Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize {tau[d]}#usize)={8-2*tau[d]}#usize :=
    UScalar.eq_of_val_eq ix.2
  unfold weights_new_loop0_loop0.body
  rw [JGo_TX2_Range.next {d}#usize 5#usize {d+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [show Array.index_usize TAU {d}#usize=ok {tau[d]}#usize from by unfold TAU;rfl,bind_tc_ok]
  simp only [lift,bind_tc_ok,ix9,ix8]
  with_unfolding_all rfl
#print axioms step{d}
'''
 if k>=3:
  point=k-3
  s+=f"theorem product : field.QM31.mul z{point}x z{point}y=ok z{point}product := by with_unfolding_all rfl\n#print axioms product\n"
  s+=f"theorem double : FIn_WeightsExtract.double z{point}x=ok x{point}_1 := by with_unfolding_all rfl\n#print axioms double\n"
  for d in range(1,5):
   n=k*5+d
   s+=f"""theorem step{d} : weights_new_loop1_loop0.body {point}#usize
    {{start:={d}#usize,«end»:=5#usize}} factors{n:02} x{point}_{d}=
      ok (.cont ({{start:={d+1}#usize,«end»:=5#usize}},factors{n+1:02},x{point}_{d+1})) := by
  have index : Usize.wrapping_add 3#usize {point}#usize={k}#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize {point}#usize (by decide))
  unfold weights_new_loop1_loop0.body
  rw [JGo_TX2_Range.next {d}#usize 5#usize {d+1}#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  simp only [lift,bind_tc_ok,index]
  with_unfolding_all rfl
#print axioms step{d}
"""

 s+=f'end AspisR1.JGo_TX2_WeightRow{k}\nend\n'
 mods[f'JGo_TX2_WeightRow{k}.lean']=s
for f,s in mods.items():
 p=R/'lean'/f
 if '--check' in sys.argv:assert p.read_text()==s,f
 else:p.write_text(s)
print('weights outputs',len(mods))
