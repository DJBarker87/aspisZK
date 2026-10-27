"""Small exact-word certificates. Each cell is one field operation, never a recurrence reduction."""
from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'lean';P=Path(__file__).resolve().parent
MOD=2147483647
zero=(0,0,0,0)
def add(x,y):return tuple((a+b)%MOD for a,b in zip(x,y))
def cm(x,y):return ((x[0]*y[0]-x[1]*y[1])%MOD,(x[0]*y[1]+x[1]*y[0])%MOD)
def mul(x,y):
 a,b=cm(x[:2],y[:2]),cm(x[2:],y[2:]);r=((2*b[0]-b[1])%MOD,(b[0]+2*b[1])%MOD)
 c,d=cm(x[:2],y[2:]),cm(x[2:],y[:2]);return ((a[0]+r[0])%MOD,(a[1]+r[1])%MOD,(c[0]+d[0])%MOD,(c[1]+d[1])%MOD)
def w(x):return f'(({x[0]},{x[1]}),({x[2]},{x[3]}))'
def powq(x,n):
 out=(1,0,0,0)
 while n:
  if n&1:out=mul(out,x)
  x=mul(x,x);n//=2
 return out
points=[tuple(map(int,m)) for m in re.findall(r'\(\((\d+),(\d+)\),\((\d+),(\d+)\)\)',(L/'JGd_LinearInputs.lean').read_text())]
assert len(points)==10
norm='norm_num [AspisV8R17.GeneratedQM31Products.qmMulWords, AspisV8R17.GeneratedQM31Linear.qmAddWords, AspisV8R17.GeneratedQM31Products.addWords, AspisV8R17.GeneratedQM31Products.subWords, AspisV8R17.GeneratedQM31Products.mulWords, AspisV8R17.GeneratedQM31Products.rWords, AspisV8R17.RawReducer.P]'
files={}
head=lambda name,imp: f'import {imp}\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen JGd_ExactWords\nattribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd\n'
tails={f:[zero]*11 for f in [0,16]};terms={f:[] for f in [0,16]}
for f in terms:
 terms[f]=[mul((3+22*j+f*(17+8*j),0,0,0),x) for j,x in enumerate(points)]
 for j in reversed(range(10)):tails[f][j]=add(terms[f][j],tails[f][j+1])
for j in reversed(range(10)):
 name=f'JGd_Linear{j:02}';imp='JGd_LinearInputs' if j==9 else f'JGd_Linear{j+1:02}'
 s=head(name,imp)
 for f in [0,16]:
  k=3+22*j+f*(17+8*j);t=terms[f][j];prev=tails[f][j+1];out=tails[f][j]
  s+=f'\ndef term{f} : W := {w(t)}\ndef sum{f} : W := {w(out)}\n'
  s+=f'theorem weighted{f} : ({k}:Q) * value (JGd_LinearInputs.point ⟨{j},by omega⟩) = value term{f} := by\n  change value {w((k,0,0,0))} * value (JGd_LinearInputs.point ⟨{j},by omega⟩) = value term{f}\n  apply mul\n  change AspisV8R17.GeneratedQM31Products.qmMulWords {w((k,0,0,0))} {w(points[j])} = {w(t)}\n  {norm}\n#print axioms weighted{f}\n'
  s+=f'theorem added{f} : value term{f} + value {w(prev)} = value sum{f} := by\n  apply add\n  change AspisV8R17.GeneratedQM31Linear.qmAddWords {w(t)} {w(prev)} = {w(out)}\n  {norm}\n#print axioms added{f}\n'
 s+=f'end AspisR1.{name}\nend\n';files[name]=s
if '--check' in sys.argv:
 for n,s in files.items():assert (L/(n+'.lean')).read_text()==s,n
else:
 for n,s in files.items():(L/(n+'.lean')).write_text(s)
(P/'JGd_CERTIFICATE_MANIFEST.json').write_text(json.dumps(dict(cells=40,hash_blocks=0,model='mask linear families 0 and 16 on retained round point',sources={n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()},linears={str(f):v[0] for f,v in tails.items()}),indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(files),'linear modules')
# Coefficient population: one checked basis call and one array write per cell.
claims={int(i):tuple(map(int,re.findall(r'(\d+)#u32',body))) for i,body in re.findall(r'def q(\d+) :[^\n]+ := ([^\n]+)',(L/'JFu_ClaimsData.lean').read_text())}
exps=[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25,1,3,5,7,9,11,15,17,19,21]
def basis(x,i):
 a,b=x[:2],x[2:]
 def iw(z):return ((-z[1])%MOD,z[0])
 def rw(z):return ((2*z[0]-z[1])%MOD,(z[0]+2*z[1])%MOD)
 return [x,(*iw(a),*iw(b)),(*rw(b),*a),(*iw(rw(b)),*iw(a))][i]
def pq(x):return f'⟨⟨{x[0]}#u32,{x[1]}#u32⟩,⟨{x[2]}#u32,{x[3]}#u32⟩⟩'
arrays=[[zero]*27];transformed=[]
for k in range(26):
 t=basis(claims[k],(k if k<16 else k-16)%4);transformed.append(t);arr=arrays[-1].copy();arr[exps[k]]=t;arrays.append(arr)
cf={};name='JGd_CoefficientData';s=head(name,'JGd_CoefficientStep')+'open Aeneas Aeneas.Std Result\nabbrev PQ := FIp_SemanticArithmetic.PQ\n'
for k,t in enumerate(transformed):s+=f'def t{k:02} : PQ := {pq(t)}\n'
for k,arr in enumerate(arrays):s+=f'def a{k:02} : ExtractedMaskCoefficientStep.Coefficients := ⟨[{",".join(pq(t) for t in arr)}],by rfl⟩\n'
s+=f'end AspisR1.{name}\nend\n';cf[name]=s
for k in range(26):
 name=f'JGd_Coefficient{k:02}';imp='JGd_CoefficientData' if k==0 else f'JGd_Coefficient{k-1:02}'
 j=k if k<16 else k-16;f=0 if k<16 else 1;cap=16 if f==0 else 10;source='c1' if f==0 else 'maskOnly';table='FACTOR_EXPONENTS' if f==0 else 'MASK_ONLY_FACTOR_EXPONENTS';t=transformed[k]
 s=head(name,imp)+'open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe\nopen JGd_CoefficientData\n'
 s+=f'theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q{k:03}) {j%4}#usize = ok t{k:02} := by\n  apply JGd_CoefficientStep.basis\n  · exact JFu_MaskInputs.{source}_canonical ⟨{j},by omega⟩\n  · change {j%4}<4;omega\n  · change ExtractedMaskTowerBasis.basisWords {w(claims[k])} {j%4} = {w(t)}\n    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]\n#print axioms basis\n'
 s+=f'theorem write : ExtractedMaskCoefficientLoop{f}.writeAt{f}\n    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.{source}) a{k:02} {j}#usize (by change {j}<{cap};omega) = a{k+1:02} := by\n  have hexp : core.convert.num.FromUsizeU8.from {exps[k]}#u8 = {exps[k]}#usize := by\n    apply UScalar.eq_of_val_eq\n    rw [core.convert.num.FromUsizeU8.from_val_eq]\n    rfl\n  have hbit : ({j}#usize &&& 3#usize) = {j%4}#usize := by decide\n  unfold ExtractedMaskCoefficientLoop{f}.writeAt{f} state_only_hiding.{table}\n  dsimp only\n  rw [hbit]\n  change a{k:02}.set (core.convert.num.FromUsizeU8.from {exps[k]}#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q{k:03}) {j%4}#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a{k+1:02}\n  rw [hexp]\n  change a{k:02}.set {exps[k]}#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q{k:03}) {j%4}#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a{k+1:02}\n  rw [basis]\n  rfl\n#print axioms write\n'
 s+=f'theorem advance (n : Nat) :\n    ExtractedMaskCoefficientLoop{f}.writeModel{f} (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.{source})\n      a{k:02} ⟨{j}#usize,{cap}#usize⟩ (n+1) =\n    ExtractedMaskCoefficientLoop{f}.writeModel{f} (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.{source})\n      a{k+1:02} ⟨{j+1}#usize,{cap}#usize⟩ n := by\n  rw [JGd_CoefficientStep.step{f} _ _ {j}#usize {cap}#usize {j+1}#usize n\n    (by change {j}<{cap};omega) (JGd_CoefficientStep.next _ _ _ (by change {j}<{cap};omega) (by rfl)),write]\n#print axioms advance\n'
 s+=f'end AspisR1.{name}\nend\n';cf[name]=s
if '--check' in sys.argv:
 for n,s in cf.items():assert (L/(n+'.lean')).read_text()==s,n
else:
 for n,s in cf.items():(L/(n+'.lean')).write_text(s)
(P/'JGd_COEFFICIENT_MANIFEST.json').write_text(json.dumps(dict(cells=26,hash_blocks=0,coefficients=arrays[-1],sources={n:hashlib.sha256(s.encode()).hexdigest() for n,s in cf.items()}),indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(cf),'coefficient modules')
# Six square/multiply certificates for exponent 26; no power normalization.
pf={};base=tails[16][0];powers={1:base}
for a,b in [(1,1),(2,2),(4,4),(8,8),(16,8),(24,2)]:powers[a+b]=mul(powers[a],powers[b])
for group,steps in enumerate([[(1,1),(2,2),(4,4)],[(8,8),(16,8),(24,2)]]):
 name=f'JGd_Power{group}';s=head(name,'JGd_LinearValue' if group==0 else 'JGd_Power0')
 for a,b in steps:
  n=a+b
  s+=f'def x{n} : W := {w(powers[n])}\n'
  s+=f'theorem product{n} : value {w(powers[a])} * value {w(powers[b])} = value x{n} := by\n  apply mul\n  change AspisV8R17.GeneratedQM31Products.qmMulWords {w(powers[a])} {w(powers[b])} = {w(powers[n])}\n  {norm}\n#print axioms product{n}\n'
  proof='by rw [pow_one]' if n==2 else 'by rw ['+','.join(f'{"JGd_Power0." if k<16 else ""}power{k}' for k in sorted(set([a,b])))+']'
  s+=f'theorem power{n} : value JGd_Linear00.sum16 ^ {n} = value x{n} := by\n  calc\n    _ = value JGd_Linear00.sum16 ^ {a} * value JGd_Linear00.sum16 ^ {b} := pow_add _ {a} {b}\n    _ = value {w(powers[a])} * value {w(powers[b])} := {proof}\n    _ = value x{n} := product{n}\n#print axioms power{n}\n'
 s+=f'end AspisR1.{name}\nend\n';pf[name]=s
if '--check' in sys.argv:
 for n,s in pf.items():assert (L/(n+'.lean')).read_text()==s,n
else:
 for n,s in pf.items():(L/(n+'.lean')).write_text(s)
(P/'JGd_POWER_MANIFEST.json').write_text(json.dumps(dict(cells=6,hash_blocks=0,power26=powers[26],sources={n:hashlib.sha256(s.encode()).hexdigest() for n,s in pf.items()}),indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(pf),'power modules')
# Twenty-six Horner cells, each transported by the existing modular-word laws.
hf={};acc=arrays[-1][26];horner={26:acc}
for j in reversed(range(26)):horner[j]=add(mul(tails[0][0],horner[j+1]),arrays[-1][j])
name='JGd_HornerData';s=head(name,'JGd_Coefficients\nimport JGd_Power1')
s+='open Aeneas Aeneas.Std\n'
s+='def coeff := ExtractedMaskHornerCaller.coefficientValue (ExtractedMaskCallerModel.populatedCoefficients (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly))\n'
s+=f'def r26 : W := {w(horner[26])}\n'
s+='def run (n : Nat) (v : Q) : Q := ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) n v\n'
s+='theorem seed : coeff 26 = value r26 := JGd_Coefficients.value ⟨26,by omega⟩\n#print axioms seed\n'
s+=f'end AspisR1.{name}\nend\n';hf[name]=s
for j in reversed(range(26)):
 name=f'JGd_Horner{j:02}';s=head(name,'JGd_HornerData' if j==25 else f'JGd_Horner{j+1:02}')
 s+='open JGd_HornerData\n'
 prev=horner[j+1];product=mul(tails[0][0],prev);out=horner[j];cw=arrays[-1][j]
 s+=f'def product : W := {w(product)}\ndef r{j:02} : W := {w(out)}\n'
 s+=f'theorem multiplied : value {w(tails[0][0])} * value {w(prev)} = value product := by\n  apply mul\n  change AspisV8R17.GeneratedQM31Products.qmMulWords {w(tails[0][0])} {w(prev)} = {w(product)}\n  {norm}\n#print axioms multiplied\n'
 s+=f'theorem added : value product + value {w(cw)} = value r{j:02} := by\n  apply add\n  change AspisV8R17.GeneratedQM31Linear.qmAddWords {w(product)} {w(cw)} = {w(out)}\n  {norm}\n#print axioms added\n'
 s+=f'theorem step : run {j+1} (value {w(prev)}) = run {j} (value r{j:02}) := by\n  unfold run\n  rw [ExtractedMaskHornerPolynomial.hornerLoopModel]\n  have hcell := JGd_Coefficients.value ⟨{j},by omega⟩\n  change coeff {j} = value (JGd_Coefficients.cell ⟨{j},by omega⟩) at hcell\n  rw [hcell]\n  change ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) {j}\n    (value {w(tails[0][0])} * value {w(prev)} + value {w(cw)}) = _\n  rw [multiplied,added]\n#print axioms step\n'
 s+=f'end AspisR1.{name}\nend\n';hf[name]=s
if '--check' in sys.argv:
 for n,s in hf.items():assert (L/(n+'.lean')).read_text()==s,n
else:
 for n,s in hf.items():(L/(n+'.lean')).write_text(s)
(P/'JGd_HORNER_MANIFEST.json').write_text(json.dumps(dict(cells=26,hash_blocks=0,horner=horner[0],sources={n:hashlib.sha256(s.encode()).hexdigest() for n,s in hf.items()}),indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(hf),'horner modules')
# The numeric mask and the unique terminal operand required by the final gate.
maskfactor=add((1,0,0,0),powers[26]);maskmul=mul(maskfactor,claims[27]);mask=add(horner[0],maskmul)
eta=tuple(map(int,re.findall(r'(\d+)#u32',re.search(r'def value14 :[^\n]+ := ([^\n]+)',(L/'JFm_Coordinates.lean').read_text()).group(1))))
running=(1645475237,1054917232,2009538975,558867101)
residual=tuple((a-b-c)%MOD for a,b,c in zip(running,mask,claims[115]))
needed=mul(residual,powq(eta,MOD**4-2));assert mul(eta,needed)==residual
name='JGd_NumericData';s=head(name,'JGd_HornerValue\nimport JGb_MaskedArithmetic')+'open Aeneas Aeneas.Std Result\n'
for n,v in [('factor',maskfactor),('weightedMask',maskmul),('maskWords',mask),('neededWords',needed),('weightedTerminal',residual),('partial',add(mask,residual))]:s+=f'def {n} : W := {w(v)}\n'
for n,v in [('mask',mask),('neededTerminal',needed),('running',running)]:
 s+=f'def {n} : FIp_SemanticArithmetic.MQ := {pq(v)}\n'
 s+=f'theorem {n}_canonical : FIp_SemanticValues.Canon {n} := by\n  change ({v[0]}<2147483647 ∧ {v[1]}<2147483647) ∧ ({v[2]}<2147483647 ∧ {v[3]}<2147483647)\n  omega\n#print axioms {n}_canonical\n'
for n,x,y,z,op in [('factor_value',(1,0,0,0),powers[26],maskfactor,'add'),('mask_product',maskfactor,claims[27],maskmul,'mul'),('mask_sum',horner[0],maskmul,mask,'add'),('terminal_product',eta,needed,residual,'mul'),('partial_value',mask,residual,add(mask,residual),'add'),('running_value',add(mask,residual),claims[115],running,'add')]:
 s+=f'theorem {n} : value {w(x)} {"+" if op=="add" else "*"} value {w(y)} = value {w(z)} := by\n  apply {op}\n  change AspisV8R17.{"GeneratedQM31Linear.qmAddWords" if op=="add" else "GeneratedQM31Products.qmMulWords"} {w(x)} {w(y)} = {w(z)}\n  {norm}\n#print axioms {n}\n'
s+=f'end AspisR1.{name}\nend\n'
if '--check' in sys.argv:assert (L/(name+'.lean')).read_text()==s,name
else:(L/(name+'.lean')).write_text(s)
(P/'JGd_NUMERIC_MANIFEST.json').write_text(json.dumps(dict(hash_blocks=0,mask=mask,needed_terminal=needed,eta=eta,last=claims[115],running=running,source=hashlib.sha256(s.encode()).hexdigest(),claim='mask arithmetic only; terminal return has not been identified with needed_terminal'),indent=2)+'\n')
print('numeric mask',mask,'required terminal',needed)
