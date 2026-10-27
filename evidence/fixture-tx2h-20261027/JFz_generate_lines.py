"""Finite per-query line certificates; actual inverse reads stay symbolic."""
from pathlib import Path
import json,re,sys
P=2147483647;OUT=Path('evidence/fixture-tx2h-20261027')
D=json.loads((OUT/'JFz_NUMERIC_PREFLIGHT.json').read_text())['queries']
def rec(a,suf=''):
 if len(a)==1:return str(a[0])+suf
 n=len(a)//2;return '⟨'+rec(a[:n],suf)+','+rec(a[n:],suf)+'⟩'
def add(a,b):return [(x+y)%P for x,y in zip(a,b)]
def sub(a,b):return [(x-y)%P for x,y in zip(a,b)]
def scale(a,b):return [x*b%P for x in a]
def mul(a,b):
 if len(a)==1:return [a[0]*b[0]%P]
 n=len(a)//2;hi=mul(a[n:],b[n:]);r=[-hi[0]%P] if n==1 else mul(hi,[2,1] if n==2 else [0,0,1,0])
 return add(mul(a[:n],b[:n]),r)+add(mul(a[:n],b[n:]),mul(a[n:],b[:n]))
def emit(path,s):
 p=Path(path)
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
A=[1923325677,606708475,390399940,1424274113,1600018693,561365806,1230057896,509172918]
REPORT=[]
for i,d in enumerate(D):
 q=10+i;pre=f'JFz_TX2_Q{i}_Line';v=[]
 for j in range(4):v.append(list(map(int,re.findall(r'(\d+)#u32',re.search(r'def value[^\n]+',Path(f'lean/JFn_Value{q}_{j}.lean').read_text())[0]))))
 ix,iy,iz=[pow(x,-1,P) for x in d['row'][2:]]
 c0=scale(sub(v[0],v[1]),1073741824*ix%P);c1=scale(sub(v[3],v[2]),1073741824*iy%P)
 h0=scale(add(add(add(v[0],v[1]),v[2]),v[3]),536870912)
 h2=scale(sub(sub(add(v[0],v[1]),v[2]),v[3]),536870912*iz%P)
 h1=scale(add(c0,c1),1073741824);h3=scale(sub(c0,c1),1073741824*iz%P)
 t2=add(h2,mul(A,h3));t1=add(h1,mul(A,t2));out=add(h0,mul(A,t1))
 REPORT.append(dict(i=i,line=out,inverses=[ix,iy,iz]))
 s=f'''import JFn_Lines
import JFw_TX2_CircleNumbers
import JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.{pre}
open Aeneas Aeneas.Std Result
abbrev FE := AspisWideTower.WideExact
abbrev FP := Port5Q1_QueryPorts.FP
'''
 for n,a in [('alpha',A),*[(f'd{k}',a) for k,a in enumerate(v)],('c0',c0),('c1',c1),('h0',h0),('h1',h1),('h2',h2),('h3',h3),('t2',t2),('t1',t1),('answer',out)]:s+=f'def {n} : FE := {rec(a)}\n'
 s+=f'def value : SAQ_WideABI.E := FIo_Install.fromE {rec(out,"#u32")}\n'
 s+='''theorem half : (2:FE)⁻¹=1073741824 := by
  apply inv_eq_of_mul_eq_one_right
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms half
'''
 exprs=[('c0_eq',f'(d0-d1)*(1073741824*{ix})=c0','d0 d1 c0'),('c1_eq',f'(d3-d2)*(1073741824*{iy})=c1','d3 d2 c1'),('h0_eq','(d0+d1+d2+d3)*536870912=h0','d0 d1 d2 d3 h0'),('h2_eq',f'(d0+d1-d2-d3)*(536870912*{iz})=h2','d0 d1 d2 d3 h2'),('h1_eq','(c0+c1)*1073741824=h1','c0 c1 h1'),('h3_eq',f'(c0-c1)*(1073741824*{iz})=h3','c0 c1 h3'),('horner2','h2+alpha*h3=t2','h2 alpha h3 t2'),('horner1','h1+alpha*t2=t1','h1 alpha t2 t1'),('horner0','h0+alpha*t1=answer','h0 alpha t1 answer')]
 for n,expr,unfold in exprs:
  s+=f'''theorem {n} : {expr} := by
  unfold {unfold}
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
#print axioms {n}
'''
 for j,iv in enumerate([ix,iy,iz]):
  s+=f'''theorem inv{j} : (S7JoinBasisMachine.decode ((JFv_TX2_Rows.value {i}).words[{j+2}]?.getD 0#u32))⁻¹=({iv}:FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal {d['row'][j+2]} {iv} (by norm_num)
theorem cast{j} : algebraMap FP FE {iv}=({iv}:FE) := map_natCast _ _
#print axioms inv{j}
#print axioms cast{j}
'''
 for j in range(4):s+=f'theorem v{j} : Port5Q1_OpeningValues.values (JFn_Values.value {i}) {j}=d{j} := rfl\n#print axioms v{j}\n'
 s+=f'''theorem formula : FoldRuntimeAlgebra.lineWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha1.scalar)
    (algebraMap FP FE {ix}) (algebraMap FP FE {iy}) (algebraMap FP FE {iz})
    (Port5Q1_OpeningValues.values (JFn_Values.value {i}))=answer := by
  have scalar : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl
  rw [scalar,cast0,cast1,cast2]
  unfold FoldRuntimeAlgebra.lineWithInverses
  rw [v0,v1,v2,v3,JFw_TX2_CircleNumbers.quarter,half,c0_eq,c1_eq,h0_eq,h2_eq,h1_eq,h3_eq,horner2,horner1,horner0]

theorem source {{C : Type}} (err : C) (seed : Port3_NativeGeometryBody.Ops C) :
    SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value {i})
      (JFv_TX2_CircleGeometry.inverse err seed {i})=ok value := by
  obtain ⟨out,run,canon⟩ := JFn_Lines.source {i} (JFv_TX2_CircleGeometry.inverse err seed {i})
  have sem := (SAQ_LineQuery.exact_line _ _ _ _ run).1
  rw [JFv_TX2_CircleGeometry.decoded err seed {i} 2,
    JFv_TX2_CircleGeometry.decoded err seed {i} 3,
    JFv_TX2_CircleGeometry.decoded err seed {i} 4,inv0,inv1,inv2,formula] at sem
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have cv : FIo_WideValues.Canon (FIo_Install.toE value) := by
    change (({out[0]}<2147483647 ∧ {out[1]}<2147483647) ∧ ({out[2]}<2147483647 ∧ {out[3]}<2147483647)) ∧
      (({out[4]}<2147483647 ∧ {out[5]}<2147483647) ∧ ({out[6]}<2147483647 ∧ {out[7]}<2147483647))
    omega
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE value) co cv sem
  have same : out=value := congrArg FIo_Install.fromE sameNative
  exact same ▸ run
#print axioms formula
#print axioms source
end AspisR1.{pre}
end
'''
 if i<2:emit('lean/'+pre+'.lean',s)
 else:
  # The gate file is assembled deterministically from the circle generator.
  # It is safe to append this independent line closure before its first compile.
  p=Path('lean/'+f'JFz_TX2_Q{i}_Gate.lean');base=(OUT/f'JFz_TX2_Q{i}_Gate_Circle.lean.txt').read_text()
  imports=re.findall(r'^import (\S+)',s,re.M)
  s=re.sub(r'^import \S+\n','',s,flags=re.M)
  for dep in imports:
   if 'import '+dep+'\n' not in base:base='import '+dep+'\n'+base
  emit(str(p),base+'\n'+s)
emit(str(OUT/'JFz_LINE_PREFLIGHT.json'),json.dumps(REPORT,indent=2)+'\n')
