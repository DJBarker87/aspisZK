"""Extend the retained explicit-value method; new JFz_TX2 modules only."""
from pathlib import Path
import re,json,sys
BASE=Path('evidence/fixture-tx2g-20261026'); OUT=Path('evidence/fixture-tx2h-20261027'); P=2147483647
V=json.loads((BASE/'JFw_POWERS.json').read_text()); A=[492967452,709301790,1617612614,599334322,1668486716,1253062525,341779229,880523595]
PENDING={}
def emit(path,s):
 PENDING[path]=s
def write(path,s):
 p=Path(path)
 if '--check' in sys.argv:assert p.read_text()==s,str(p)
 else:p.write_text(s)
def rec(a,suf=''):
 if len(a)==1:return str(a[0])+suf
 n=len(a)//2;return '⟨'+rec(a[:n],suf)+','+rec(a[n:],suf)+'⟩'
def add(a,b):return [(x+y)%P for x,y in zip(a,b)]
def mul(a,b):
 if len(a)==1:return [a[0]*b[0]%P]
 n=len(a)//2;hi=mul(a[n:],b[n:]);r=[-hi[0]%P] if n==1 else mul(hi,[2,1] if n==2 else [0,0,1,0])
 return add(mul(a[:n],b[:n]),r)+add(mul(a[:n],b[n:]),mul(a[n:],b[:n]))
def fold(x):return (x&P)+(x>>31)
def raw(a,b):
 a,b,c,d,e,f,g,h=a+b;pp=P*P;mask=(1<<64)-1
 u=fold((c*g+pp-d*h)&mask);v=fold((c*h+d*g)&mask)
 return [(a*e+pp-b*f+2*u+3*P-v)&mask,(a*f+b*e+u+2*v)&mask,(a*g+c*e+2*pp-b*h-d*f)&mask,(a*h+b*g+c*f+d*e)&mask]
def nums(s):return list(map(int,re.findall(r'(\d+)#u32',s)))
def decl(file,name):return re.search(rf'def {name}[^\n]+',Path(file).read_text())[0]
DATA=[]
for i in range(12):
 q=10+i;heads=[];tails=[];raws=[]
 for slot in range(4):
  scalars=nums(decl(f'lean/JFr_TX2_Slot{q}_{slot}.lean','values'))
  heads.append([sum(V[t][j]*scalars[t] for t in range(26))%P for j in range(8)])
  before=[0]*8
  for kind,k in enumerate([28,26,27]):
   Q=nums(decl(f'lean/JFr_TX2_Tails{q}.lean',f'value{kind}_{slot}'))
   R=raw(V[k][:4],Q)+raw(V[k][4:],Q);after=[x+fold(y) for x,y in zip(before,R)]
   raws.append(dict(slot=slot,kind=kind,k=k,q=Q,raws=[R[:4],R[4:]],before=before,after=after));before=after
  tails.append([x%P for x in before])
 dots=[add(h,t) for h,t in zip(heads,tails)]
 row=nums(decl(f'lean/JFv_TX2_Row{q}.lean','value'));ix,iy=[pow(x,-1,P) for x in row[:2]]
 H=[]
 for signs,scale in [([1,1,1,1],536870912),([1,-1,-1,1],536870912*iy%P),([1,1,-1,-1],536870912*ix%P),([1,-1,1,-1],536870912*ix*iy%P)]:H.append([sum(signs[s]*dots[s][j] for s in range(4))*scale%P for j in range(8)])
 t2=add(H[2],mul(A,H[3]));t1=add(H[1],mul(A,t2));circle=add(H[0],mul(A,t1))
 vals=Path('lean/JFn_Values.lean').read_text();query=int(re.search(rf'\| {i} => (\d+)#u32',Path('lean/JFv_TX2_Rows.lean').read_text().split('def query')[1])[1]) if i<11 else 14297
 selected=nums(decl(f'lean/JFn_Value{q}_{query%4}.lean','value'))
 DATA.append(dict(i=i,query=query,heads=heads,tails=tails,dots=dots,raws=raws,row=row,ix=ix,iy=iy,H=H,t2=t2,t1=t1,circle=circle,selected=selected,match=circle==selected))
emit(str(OUT/'JFz_NUMERIC_PREFLIGHT.json'),json.dumps(dict(status='Python arithmetic proposals only; not kernel gate proofs',queries=DATA),indent=2)+'\n')
# Generic reusable templates are read only. No inherited file is overwritten.
for i in range(1,12):
 d=DATA[i];q=10+i;pre=f'JFz_TX2_Q{i}_'
 def transform(s):
  for name in ['Head','Raw','Tail','Dot','Circle','Query']:
   # preserve reusable generic helpers
   if name=='Head': names=['Head00','Head0Lo','Head0Hi','Head0','Head1Lo','Head1Hi','Head1','Head2Lo','Head2Hi','Head2','Head3Lo','Head3Hi','Head3']
   elif name=='Raw':names=[f'Raw{slot}{k}' for slot in range(4) for k in range(3)]
   elif name=='Tail':names=[f'Tail{slot}' for slot in range(4)]
   elif name=='Dot':names=['Dots0']+[f'Dot{slot}' for slot in range(4)]
   elif name=='Circle':names=['CircleNumbers','CircleCoefficients','CircleFormula']
   else:names=['Query0']
   for n in sorted(names,key=len,reverse=True):s=re.sub(r'JFw_TX2_'+n+r'\b',pre+n,s)
  s=s.replace('JFw_TX2_HeadTransport','JFz_TX2_HeadTransport').replace('JFn_Values.position 0',f'JFn_Values.position {i}').replace('JFr_TX2_Tails10',f'JFr_TX2_Tails{q}')
  return s
 # 8 head numeric halves plus four source-identification modules.
 for slot in range(4):
  scalars=nums(decl(f'lean/JFr_TX2_Slot{q}_{slot}.lean','values'));h=d['heads'][slot]
  for part,js in [('Lo',range(4)),('Hi',range(4,8))]:
   mod=pre+f'Head{slot}{part}';s=f'import JFz_TX2_HeadTransport\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{mod}\nopen Aeneas Aeneas.Std Result\n'
   for j in js:
    expr='0'+''.join(f'+{V[t][j]}*{scalars[t]}' for t in range(26))
    s+=f'''theorem lane{j} : JFv_TX2_InnerMeaning.sum {i} {slot} {j} 0 26%2147483647={h[j]} := by
  rw [JFz_TX2_HeadTransport.source]
  simp only [JFz_TX2_HeadTransport.sum]
  change ({expr})%2147483647={h[j]}
  norm_num
#print axioms lane{j}
'''
   s+=f'end AspisR1.{mod}\nend\n';emit('lean/'+mod+'.lean',s)
  s=transform(Path(f'lean/JFw_TX2_Head{slot}.lean').read_text())
  if slot==0:s=s.replace('import '+pre+'Head00\n','').replace(pre+'Head00.lane0',pre+'Head0Lo.lane0')
  s=s.replace(f'sum 0 {slot}',f'sum {i} {slot}').replace(f'HeadFlat.source 0 {slot}',f'HeadFlat.source {i} {slot}')
  old=nums(decl(f'lean/JFw_TX2_Head{slot}.lean','value'));s=s.replace(rec(old,'#u32'),rec(h,'#u32'))
  for j in range(8):s=s.replace(f'26%2147483647={old[j]}',f'26%2147483647={h[j]}')
  # Inline the small coordinate equations after their symbolic transport lemma.
  for part in ['Lo','Hi']:
   half=PENDING['lean/'+pre+f'Head{slot}{part}.lean']
   body=half[half.index('theorem lane'):half.index('end AspisR1.')]
   s=s.replace('import '+pre+f'Head{slot}{part}\n','')
   for j in (range(4) if part=='Lo' else range(4,8)):
    pat=rf'theorem lane{j}[^\n]+\n'
    theorem=re.search(rf'theorem lane{j}.*?(?=theorem lane|#print axioms lane{j})',body,re.S)[0]
    s=re.sub(pat,lambda m:theorem,s)
  s='import JFz_TX2_HeadTransport\n'+s
  emit('lean/'+pre+f'Head{slot}.lean',s)
 # Raw proofs: retain the checked source template, changing only finite operands.
 oldraw=json.loads((BASE/'JFw_RAW.json').read_text())
 for old,new in zip(oldraw,d['raws']):
  name=f"Raw{new['slot']}{new['kind']}";s=Path('lean/JFw_TX2_'+name+'.lean').read_text()
  # Token substitution simultaneously avoids replacing a replacement.
  mapping={str(a):str(b) for a,b in zip(old['q']+old['before']+old['after']+sum(old['raws'],[]),new['q']+new['before']+new['after']+sum(new['raws'],[])) if a!=b}
  # zero initial coordinates stay zero; repeated operand values have consistent mappings.
  s=re.sub(r'\b\d+\b',lambda m:mapping.get(m[0],m[0]),s)
  emit('lean/'+pre+name+'.lean',transform(s))
 for slot in range(4):
  s=Path(f'lean/JFw_TX2_Tail{slot}.lean').read_text();old=oldraw[slot*3+2]['after'];new=d['raws'][slot*3+2]['after']
  mapping={str(a):str(b) for a,b in zip(old+[x%P for x in old],new+[x%P for x in new])}
  s=re.sub(r'\b\d+(?=%2147483647|#u32)',lambda m:mapping.get(m[0],m[0]),s)
  emit('lean/'+pre+f'Tail{slot}.lean',transform(s))
  s=Path(f'lean/JFw_TX2_Dot{slot}.lean').read_text()
  orig=json.loads((BASE/'JFw_NUMERIC_PREFLIGHT.json').read_text());oh=json.loads((BASE/'JFw_HEADS.json').read_text())[slot]
  mapping={str(a):str(b) for a,b in zip(oh+orig['tails'][slot]+orig['dots'][slot],d['heads'][slot]+d['tails'][slot]+d['dots'][slot])}
  s=re.sub(r'\b\d+\b',lambda m:mapping.get(m[0],m[0]),s).replace(f'Slot.source 0 {slot}',f'Slot.source {i} {slot}')
  emit('lean/'+pre+f'Dot{slot}.lean',transform(s))
 s=transform(Path('lean/JFw_TX2_Dots0.lean').read_text()).replace('Dots.value 0=value',f'Dots.value {i}=value')
 emit('lean/'+pre+'Dots0.lean',s)
 # Circle numerical stages retain the sparse finite field proof equations.
 oldD=DATA[0]
 oldnums=[243259912,1029545577]+sum(oldD['H'],[])+oldD['t2']+oldD['t1']+oldD['circle']+sum(oldD['dots'],[])
 newnums=[d['ix'],d['iy']]+sum(d['H'],[])+d['t2']+d['t1']+d['circle']+sum(d['dots'],[])
 mapping={str(a):str(b) for a,b in zip(oldnums,newnums)}
 for name in ['CircleNumbers','CircleCoefficients','CircleFormula']:
  s=Path('lean/JFw_TX2_'+name+'.lean').read_text();s=re.sub(r'\b\d+\b',lambda m:mapping.get(m[0],m[0]),s)
  emit('lean/'+pre+name+'.lean',transform(s))
 # Actual circle formula on this query; inverses are separately checked small modular facts.
 mod=pre+'Query'
 s=f'''import {pre}CircleFormula
import JFv_TX2_Query0Inverse
set_option autoImplicit false
noncomputable section
namespace AspisR1.{mod}
open Aeneas Aeneas.Std Result
abbrev FP := Port5Q1_QueryPorts.FP
def selected : SAQ_WideABI.E := SAQ_RecordDecode.fromRecord JFn_Value{q}_{d['query']%4}.value
'''
 for name,v,iv in [('x',d['row'][0],d['ix']),('y',d['row'][1],d['iy'])]:
  s+=f'''theorem {name} : (S7JoinBasisMachine.decode (JFv_TX2_Rows.value {i}).{name})⁻¹=({iv} : FP) := by
  exact JFv_TX2_Query0Inverse.reciprocal {v} {iv} (by norm_num)
#print axioms {name}
'''
 s+=f'''theorem selected_read : Array.index_usize (JFn_Values.value {i}) {d['query']%4}#usize=ok selected := JFn_Values{q}.selected

def Goal {{C : Type}} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Prop :=
  FIp_CircleQuery.circle JFq_Alpha0.scalar (JFs_TX2_Dots.value {i})
    (JFv_TX2_CircleGeometry.inverse err seed {i})=ok selected

theorem source {{C : Type}} (err : C) (seed : Port3_NativeGeometryBody.Ops C) : Goal err seed := by
  obtain ⟨out,run,canon,sem⟩ := JFv_TX2_CircleGeometry.source err seed {i}
  rw [x,y,{pre}Dots0.source,{pre}CircleFormula.formula] at sem
  have selectedValue : {pre}CircleNumbers.value=CheckpointBytes5Output.ofE selected := rfl
  have csel : FIo_WideValues.Canon (FIo_Install.toE selected) := by
    change (({d['selected'][0]}<2147483647 ∧ {d['selected'][1]}<2147483647) ∧ ({d['selected'][2]}<2147483647 ∧ {d['selected'][3]}<2147483647)) ∧
      (({d['selected'][4]}<2147483647 ∧ {d['selected'][5]}<2147483647) ∧ ({d['selected'][6]}<2147483647 ∧ {d['selected'][7]}<2147483647))
    omega
  have co : FIo_WideValues.Canon (FIo_Install.toE out) := (SAQ_WideABI.w_canonical out).mp canon
  have sameNative := JFw_TX2_ValueUnique.native (FIo_Install.toE out) (FIo_Install.toE selected) co csel (sem.trans selectedValue)
  have same : out=selected := congrArg FIo_Install.fromE sameNative
  exact run.trans (congrArg Result.ok same)
#print axioms selected_read
#print axioms source
end AspisR1.{mod}
end
'''
 emit('lean/'+mod+'.lean',s)
print('Python proposed circle matches:',[d['match'] for d in DATA])

# Each slot is a small finite closure: symbolic head lanes, three raw pushes,
# finish and addition. Imports precede the declarations; no recurrence unfolds.
for path,s in list(PENDING.items()):
 if not re.search(r'lean/JFz_TX2_Q(?:[2-9]|10|11)_',path) and not (re.search(r'Head[0-3](Lo|Hi)\.lean$',path) and not path.endswith('Head0Lo.lean')):write(path,s)
for i in range(2,12):
 pre=f'JFz_TX2_Q{i}_'
 groups={pre+f'Slot{k}':[pre+f'Head{k}']+[pre+f'Raw{k}{r}' for r in range(3)]+[pre+f'Tail{k}',pre+f'Dot{k}'] for k in range(4)}
 groups[pre+'Gate']=[pre+x for x in ['Dots0','CircleNumbers','CircleCoefficients','CircleFormula','Query']]
 provider={m:g for g,ms in groups.items() for m in ms}
 for g,ms in groups.items():
  imports=[];bodies=[]
  for m in ms:
   s=PENDING['lean/'+m+'.lean']
   for dep in re.findall(r'^import (\S+)',s,re.M):
    dep=provider.get(dep,dep)
    if dep!=g and dep not in imports:imports.append(dep)
   bodies.append(re.sub(r'^import \S+\n','',s,flags=re.M))
  write((str(OUT)+'/'+g+'_Circle.lean.txt') if g.endswith('Gate') else ('lean/'+g+'.lean'),''.join('import '+dep+'\n' for dep in imports)+'\n'.join(bodies))
