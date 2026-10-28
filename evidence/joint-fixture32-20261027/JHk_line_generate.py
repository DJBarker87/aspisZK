from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2]; D=Path(__file__).resolve().parent; P=2147483647

def add(a,b):return tuple((x+y)%P for x,y in zip(a,b))
def sub(a,b):return tuple((x-y)%P for x,y in zip(a,b))
def cm(a,b):return ((a[0]*b[0]-a[1]*b[1])%P,(a[0]*b[1]+a[1]*b[0])%P)
def qm(a,b):return add(cm(a[:2],b[:2]),cm((2,1),cm(a[2:],b[2:])))+add(cm(a[:2],b[2:]),cm(a[2:],b[:2]))
def wide(a,b):return add(qm(a[:4],b[:4]),qm((0,0,1,0),qm(a[4:],b[4:])))+add(qm(a[:4],b[4:]),qm(a[4:],b[:4]))
def scale(a,n):return tuple(x*n%P for x in a)
def literal(a):
 if len(a)==2:return '⟨'+','.join(map(str,a))+'⟩'
 return '⟨'+literal(a[:len(a)//2])+','+literal(a[len(a)//2:])+'⟩'
def raw_scalar(name):
 s=(R/f'lean/JFq_{name}.lean').read_text();line=next(x for x in s.splitlines() if x.startswith('def decoded'))
 return tuple(map(int,re.findall(r'(\d+)#u32',line)))
alpha=raw_scalar('Alpha1');rho=raw_scalar('Rho');retained_rhs=raw_scalar('Rhs');power=(1,0,0,0);rhs=(0,)*8;data=[]
for i in range(10):
 s=(R/f'lean/JGw_Values{i}.lean').read_text();vs=[tuple(map(int,re.findall(r'(\d+)#u32',x))) for x in s.splitlines() if x.startswith('def value : AspisR1RecordParser')];assert len(vs)==4
 row=next(x for x in (R/f'lean/JGp_Row{i}.lean').read_text().splitlines() if x.startswith('def value :'))
 coords=list(map(int,re.findall(r'(\d+)#u32',row))); inv=[pow(x,-1,P) for x in coords[2:]];ix,iy,iz=inv
 a,b,c,d=vs
 h0=scale(add(add(add(a,b),c),d),pow(4,-1,P));h2=scale(sub(sub(add(a,b),c),d),pow(4,-1,P)*iz%P)
 c0=scale(sub(a,b),pow(2,-1,P)*ix%P);c1=scale(sub(d,c),pow(2,-1,P)*iy%P)
 h1=scale(add(c0,c1),pow(2,-1,P));h3=scale(sub(c0,c1),pow(2,-1,P)*iz%P)
 t2=add(h2,wide(alpha,h3));t1=add(h1,wide(alpha,t2));value=add(h0,wide(alpha,t1))
 rhs=add(rhs,wide(value,power+(0,)*4));power=qm(power,rho)
 data.append(dict(i=i,values=vs,coords=coords,inverses=inv,alpha=alpha,c0=c0,c1=c1,h0=h0,h1=h1,h2=h2,h3=h3,t2=t2,t1=t1,value=value,rhs=rhs,power=power))
preflight=json.dumps(dict(rows=data,retained_rhs=retained_rhs,computed_rhs=rhs,rhs_matches=rhs==retained_rhs),indent=2)+'\n'
if '--check' in sys.argv:assert (D/'JHk_LINE_PREFLIGHT.json').read_text()==preflight
else:(D/'JHk_LINE_PREFLIGHT.json').write_text(preflight)
print('Ten-query rhs preflight:',rhs,'retained:',retained_rhs,'match:',rhs==retained_rhs)
if rhs!=retained_rhs:raise SystemExit('Actual numerical rhs preflight mismatch; no certificates emitted')
for row in data:
 i=row['i'];a,b,c,d=[f'v{j}' for j in range(4)];ix,iy,iz=row['inverses']
 lines=[f'import JGw_Line{i}', 'import JGw_Inverses','import JFv_TX2_Query0Inverse','set_option autoImplicit false','noncomputable section',f'namespace AspisR1.JHk_Line{i:02}', 'open Aeneas Aeneas.Std Result', 'abbrev FE := AspisWideTower.WideExact','abbrev inverse := JGw_Inverses.inverse () JGp_Seeds.geometry '+str(i)]
 lines.insert(3,'import JGp_Seeds')
 for j,v in enumerate(row['values']):lines.append(f'def v{j} : FE := {literal(v)}')
 for k in ['alpha','c0','c1','h0','h1','h2','h3','t2','t1','value']:lines.append(f'def {k} : FE := {literal(row[k])}')
 for j,label in [(2,'X'),(3,'Y'),(4,'Z')]:
  n=row['inverses'][j-2];v=row['coords'][j]
  lines += [f'theorem inv{label} : S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse {j})=({n} : Port5Q1_QueryPorts.FP) := by',f'  rw [JGw_Inverses.decoded]',f'  exact JFv_TX2_Query0Inverse.reciprocal {v} {n} (by norm_num)',f'#print axioms inv{label}']
 equations=[('coef0','(v0+v1+v2+v3)*536870912','h0'),('coef2',f'(v0+v1-v2-v3)*(536870912*{iz})','h2'),('diff0',f'(v0-v1)*(1073741824*{ix})','c0'),('diff1',f'(v3-v2)*(1073741824*{iy})','c1'),('coef1','(c0+c1)*1073741824','h1'),('coef3',f'(c0-c1)*(1073741824*{iz})','h3'),('horner2','h2+alpha*h3','t2'),('horner1','h1+alpha*t2','t1'),('horner0','h0+alpha*t1','value')]
 for name,lhs,rhsname in equations:
  deps=[k for k in ['v0','v1','v2','v3','alpha','c0','c1','h0','h1','h2','h3','t2','t1','value'] if re.search(r'\b'+k+r'\b',lhs+' '+rhsname)]
  lines += [f'theorem {name} : {lhs}={rhsname} := by','  unfold '+' '.join(deps),'  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,', '    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide',f'#print axioms {name}']
 lines += [f'theorem formula : FoldRuntimeAlgebra.lineWithInverses alpha ({ix}:FE) ({iy}:FE) ({iz}:FE)', '    (fun j : Fin 4 => ![v0,v1,v2,v3] j)=value := by', '  have e0 : (![v0,v1,v2,v3] : Fin 4 → FE) 0=v0 := rfl','  have e1 : (![v0,v1,v2,v3] : Fin 4 → FE) 1=v1 := rfl','  have e2 : (![v0,v1,v2,v3] : Fin 4 → FE) 2=v2 := rfl','  have e3 : (![v0,v1,v2,v3] : Fin 4 → FE) 3=v3 := rfl','  unfold FoldRuntimeAlgebra.lineWithInverses', '  simp only [e0,e1,e2,e3,JHk_LineConstants.half,JFw_TX2_CircleNumbers.quarter]','  rw [coef0,coef2,diff0,diff1,coef1,coef3,horner2,horner1,horner0]','#print axioms formula',f'theorem source : CheckpointBytes5Output.ofE (JGw_Line{i}.value inverse)=value := by',f'  have h := (SAQ_LineQuery.exact_line JFq_Alpha1.scalar JGw_Values{i}.value inverse (JGw_Line{i}.value inverse)',f'    (JGw_Line{i}.returned inverse)).1', '  rw [invX,invY,invZ] at h', '  have a : CheckpointBytes5Output.ofE JFq_Alpha1.scalar=alpha := rfl']
 for n in [ix,iy,iz]:lines.append(f'  have map{n} : algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE {n}=({n}:FE) := map_natCast _ _')
 lines += ['  have vs : Port5Q1_OpeningValues.values JGw_Values'+str(i)+'.value=(fun j : Fin 4 => ![v0,v1,v2,v3] j) := by', '    funext j','    fin_cases j <;> rfl',f'  rw [a,map{ix},map{iy},map{iz},vs,formula] at h','  exact h','#print axioms source',f'end AspisR1.JHk_Line{i:02}','end']
 # The quarter lemma has the same field and is already proved in the predecessor.
 lines.insert(3,'import JHk_LineConstants')
 target=R/f'lean/JHk_Line{i:02}.lean';expected='\n'.join(lines)+'\n'
 if '--check' in sys.argv:assert target.read_text()==expected,str(target)
 else:target.write_text(expected)
