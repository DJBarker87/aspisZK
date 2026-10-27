from pathlib import Path
import sys
import re
R=Path(__file__).resolve().parents[2];P=2147483647

def ns(s):return list(map(int,re.findall(r'(\d+)#u32',s)))
def add(a,b):return [(x+y)%P for x,y in zip(a,b)]
def sub(a,b):return [(x-y)%P for x,y in zip(a,b)]
def scale(a,n):return [x*n%P for x in a]
def mul(a,b):
 if len(a)==1:return [a[0]*b[0]%P]
 n=len(a)//2;nr={1:[P-1],2:[2,1],4:[0,0,1,0]}[n]
 return add(mul(a[:n],b[:n]),mul(nr,mul(a[n:],b[n:]))),add(mul(a[:n],b[n:]),mul(a[n:],b[:n]))
def wm(a,b):
 def flat(x):
  if isinstance(x,int):return [x]
  return sum((flat(y) for y in x),[])
 return flat(mul(a,b))
# recursively flatten at each multiplication level
old=mul
def mul(a,b):
 if len(a)==1:return [a[0]*b[0]%P]
 n=len(a)//2;nr={1:[P-1],2:[2,1],4:[0,0,1,0]}[n]
 return add(mul(a[:n],b[:n]),mul(nr,mul(a[n:],b[n:])))+add(mul(a[:n],b[n:]),mul(a[n:],b[:n]))
def wide(a):
 a=list(map(str,a));return f'⟨⟨⟨{a[0]},{a[1]}⟩,⟨{a[2]},{a[3]}⟩⟩,⟨⟨{a[4]},{a[5]}⟩,⟨{a[6]},{a[7]}⟩⟩⟩'
alpha=ns((R/'lean/JFq_Alpha0.lean').read_text().split('def decoded :')[1].split('theorem decode')[0])
normal='AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P'
for i in range(10):
 text=(R/f'lean/JHa_Dots{i}.lean').read_text();dots=[ns(re.search(rf'def value{j} :.*? := (.*?)\n',text)[1]) for j in range(4)]
 row=ns((R/f'lean/JGp_Row{i}.lean').read_text().split('def value :')[1].split('theorem')[0]);x,y=row[:2];ix=pow(x,-1,P);iy=pow(y,-1,P);q=pow(4,-1,P)
 d0,d1,d2,d3=dots
 hs=[scale(add(add(add(d0,d1),d2),d3),q),scale(add(sub(sub(d0,d1),d2),d3),q*iy),scale(sub(sub(add(d0,d1),d2),d3),q*ix),scale(sub(add(sub(d0,d1),d2),d3),q*ix*iy)]
 t2=add(hs[2],mul(alpha,hs[3]));t1=add(hs[1],mul(alpha,t2));v=add(hs[0],mul(alpha,t1))
 idx=int(re.search(rf'theorem word{i} :.*?=([0-9]+)#u32', (R/'lean/JFq_QueryWords.lean').read_text())[1])%4
 target=ns(re.findall(r'def value : AspisR1RecordParser.field.wide_exact.WideExact := packed (.*?)\n',(R/f'lean/JGw_Values{i}.lean').read_text())[idx])
 assert v==target,(i,v,target)
 s=f'''import JGr_Geometry
import JFw_TX2_CircleNumbers
import JHa_Dots{i}
import JGw_Circle{i}
import JGw_Values{i}
import JFv_TX2_Query0Inverse
import JFw_TX2_ValueUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Circle{i}
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JGw_Value{i:02}_{idx}.value
'''
 for j in range(4):s+=f'def d{j} : FE := {wide(dots[j])}\ndef h{j} : FE := {wide(hs[j])}\n'
 s+=f'def alpha : FE := {wide(alpha)}\ndef t2 : FE := {wide(t2)}\ndef t1 : FE := {wide(t1)}\ndef value : FE := {wide(v)}\n'
 s+=f'''theorem invX : (S7JoinBasisMachine.decode (JGp_Rows.value {i}).x)⁻¹=({ix} : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal {x} {ix} (by norm_num)
theorem invY : (S7JoinBasisMachine.decode (JGp_Rows.value {i}).y)⁻¹=({iy} : Port5Q1_QueryPorts.FP) :=
  JFv_TX2_Query0Inverse.reciprocal {y} {iy} (by norm_num)
#print axioms invX
#print axioms invY
'''
 formulas=[f'(d0+d1+d2+d3)*536870912',f'(d0-d1-d2+d3)*(536870912*{iy})',f'(d0+d1-d2-d3)*(536870912*{ix})',f'(d0-d1+d2-d3)*(536870912*{ix}*{iy})']
 for j,f in enumerate(formulas):
  s+=f'''theorem coefficient{j} : {f}=h{j} := by
  unfold d0 d1 d2 d3 h{j}
  ext <;> norm_num [{normal}] <;> decide
#print axioms coefficient{j}
'''
 for n,lhs,rhs in [(2,'h2+alpha*h3','t2'),(1,'h1+alpha*t2','t1'),(0,'h0+alpha*t1','value')]:
  names={2:'h2 alpha h3 t2',1:'h1 alpha t2 t1',0:'h0 alpha t1 value'}[n]
  s+=f'''theorem horner{n} : {lhs}={rhs} := by
  unfold {names}
  ext <;> norm_num [{normal}] <;> decide
#print axioms horner{n}
'''
 s+=f'''theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE {ix})
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE {iy})
    (Port5Q1_OpeningValues.values JHa_Dots{i}.value)=value := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha0.scalar=alpha := rfl
  have xm : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE {ix}=({ix}:FE) := map_natCast _ _
  have ym : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE {iy}=({iy}:FE) := map_natCast _ _
  have v0 : Port5Q1_OpeningValues.values JHa_Dots{i}.value 0=d0 := rfl
  have v1 : Port5Q1_OpeningValues.values JHa_Dots{i}.value 1=d1 := rfl
  have v2 : Port5Q1_OpeningValues.values JHa_Dots{i}.value 2=d2 := rfl
  have v3 : Port5Q1_OpeningValues.values JHa_Dots{i}.value 3=d3 := rfl
  rw [scalar,xm,ym]
  unfold FoldRuntimeAlgebra.circleWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms formula

theorem source : FIp_CircleQuery.circle JFq_Alpha0.scalar JGw_Dots{i}.value
    (JGw_Inverses.inverse () JGp_Seeds.geometry {i})=ok selected := by
  obtain ⟨out,run,canon,sem⟩ := JGw_Circle{i}.source () JGp_Seeds.geometry
  rw [invX,invY,JHa_Dots{i}.source,formula] at sem
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change (({target[0]}<2147483647 ∧ {target[1]}<2147483647) ∧ ({target[2]}<2147483647 ∧ {target[3]}<2147483647)) ∧
      (({target[4]}<2147483647 ∧ {target[5]}<2147483647) ∧ ({target[6]}<2147483647 ∧ {target[7]}<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have selectedValue : value=CheckpointBytes5Output.ofE selected := rfl
  have sameNative := JFw_TX2_ValueUnique.native _ _ co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms source
end AspisR1.JHa_Circle{i}
end
'''
 dst=R/f'lean/JHa_Circle{i}.lean'
 if '--check' in sys.argv: assert dst.read_text()==s,str(dst)
 else: dst.write_text(s)
