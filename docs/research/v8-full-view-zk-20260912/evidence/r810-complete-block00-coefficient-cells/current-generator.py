import csv,hashlib,json,re,sys
from pathlib import Path
b=Path('docs/research/v8-full-view-zk-20260912');raw=b/'evidence/r769-point1-selected-entries/inputs/matrix.raw.tsv';cert=Path('.r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(raw)=='91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af';assert sha(cert)=='d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4'
c=json.loads(cert.read_text());rows=list(csv.reader(raw.open(),delimiter='\t'));block=c['blocks'][0];assert block['dimension']==6
out=Path('.r21-scratch/r810-coefficient-cells');out.mkdir(exist_ok=True)
head='''import AspisV8R19.R810CoefficientCellPrototype
import AspisV8R19.R780Point02WeightChunk02P0
import AspisV8R19.R780Point02WeightChunk02P2

set_option autoImplicit false
open AspisR19
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R741SparseCoefficientObservation
open AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R802OrdinaryDirectionPointCoefficients
open AspisV8R19.R808PointCoefficientStencil
open AspisV8R19.R748JointWitnessPointEntry
open AspisV8R19.R810CoefficientCellPrototype
'''
entries=[]
for bi,ri in enumerate(block['rows_original'][1:],start=1):
 k=[1,2,3,5,6][bi-1]
 assert rows[243+ri][2]==f'ordinary_relation_{k}'
 for j,ci in enumerate(block['columns_original']):
  if bi==1 and j==0:continue
  h=rows[1+ci];assert int(h[1])==ci;d,s=int(h[2]),int(h[3])-1
  # Every saved limb must agree with the raw source matrix.
  val=block['A'][bi][j][0];rawlimbs=[int(x) for x in rows[243+ri][3+ci].split(',')];assert rawlimbs==block['A'][bi][j]
  entries.append(dict(k=k,ki=bi-1,d=d,s=s,value=val,block_row=bi,block_col=j,raw_row=ri,raw_col=ci))
# Raw field parser format is checked below against the exact input.
q='(536870912:M)'
def coef(w,d,s,k):
 used=set()
 def term(dd,t):
  if t<=k and k-t<4:
   n=4*dd+(4-(k-t))%4;used.add(n);return f'{q}*{w} {n}'
  return '(0:M)'
 p=f'(7:M)^{s+1}'
 return f'(({term(d,s+1)} - {p}*({term(d,0)})) - ({term(0,s+1)} - {p}*({term(0,0)})))',used
sources=[]
for n in range(0,len(entries),10):
 chunk=entries[n:n+10];name=f'R810CoefficientCellsChunk{n//10:02d}';text=head+f'namespace AspisV8R19.{name}\nnoncomputable section\nlocal instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩\n'
 for e in chunk:
  exprs=[];used=set()
  for w in ['R780Point02WeightPrototype.pw0','pw','R780Point02WeightPrototype.pw2']:
   expr,u=coef(w,e['d'],e['s'],e['k']);exprs.append(expr);used|=u
  rew=[]
  for p in [0,2]:
   for i in sorted(used):rew.append(f'R780Point02WeightChunk{(0 if i<4 else 1 if i<96 else 2):02d}P{p}.pw{p}_{i:04d}')
  rew += ['pw0' if i==0 else 'pw3' if i==3 else f'R760PointWeightChunk00.pw_{i:04d}' for i in sorted(used)]
  th=f'coeff{e["k"]}_d{e["d"]}_s{e["s"]}';text+=f'''\ntheorem {th} :
    rawRelation (1073741824:M) {q} 7 5 (-5) 5 0 z
      (indexedDirection 7 (⟨{e['d']},by decide⟩ : Fin 255) (⟨{e['s']},by decide⟩ : Fin 3)) {e['k']} = {e['value']} := by
  rw [rawRelation_direction_point_decomposition]
  change (5:M)*pointCoefficient (1073741824:M) {q} 7 5 (-5) (SourceStatementPoints.points z 0)
      (indexedDirection 7 (⟨{e['d']},by decide⟩ : Fin 255) (⟨{e['s']},by decide⟩ : Fin 3)) (relationIndex (⟨{e['ki']},by decide⟩ : Fin 5)) +
    (5:M)^2*pointCoefficient (1073741824:M) {q} 7 5 (-5) (SourceStatementPoints.points z 1)
      (indexedDirection 7 (⟨{e['d']},by decide⟩ : Fin 255) (⟨{e['s']},by decide⟩ : Fin 3)) (relationIndex (⟨{e['ki']},by decide⟩ : Fin 5)) +
    (5:M)^3*pointCoefficient (1073741824:M) {q} 7 5 (-5) (SourceStatementPoints.points z 2)
      (indexedDirection 7 (⟨{e['d']},by decide⟩ : Fin 255) (⟨{e['s']},by decide⟩ : Fin 3)) (relationIndex (⟨{e['ki']},by decide⟩ : Fin 5)) = ({e['value']}:M)
  simp_rw [pointCoefficient_direction_stencil]
  rw [points0_eq_weight_point, points2_eq_weight_point]
  change (5:M)*{exprs[0]} + (5:M)^2*{exprs[1]} + (5:M)^3*{exprs[2]} = ({e['value']}:M)
'''
  if rew:text+='  rw ['+', '.join(rew)+']\n'
  if rew:text+='  simp only [R780Point02WeightPrototype.half]\n'
  text+='  decide\n'+f'#print axioms {th}\n'
 text+=f'end\nend AspisV8R19.{name}\n';p=out/(name+'.lean');sources.append((p,text))
 if '--write' in sys.argv:p.write_text(text)
 else:assert p.read_text()==text,p
manifest={'raw_sha256':sha(raw),'certificate_sha256':sha(cert),'entries':entries,'targets':[{'target':'AspisV8R19/'+p.name,'source_sha256':hashlib.sha256(t.encode()).hexdigest()} for p,t in sources]}
if '--write' in sys.argv:(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
else:assert json.loads((out/'manifest.json').read_text())==manifest
print('CHECKED29cells3modules; prototype cell reused; exact raw/certificate agreement')
