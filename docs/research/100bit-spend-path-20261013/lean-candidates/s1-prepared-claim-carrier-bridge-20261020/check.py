from pathlib import Path
import json,hashlib,re,subprocess
D=Path(__file__).resolve().parent
R=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=D,text=True).strip())
P=D.parent.parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
M=json.loads((D/'manifest.json').read_text())
for row in (D/'SHA256SUMS').read_text().splitlines():
 h,f=row.split('  ',1);assert sha(D/f)==h,f
for m in M['modules']:
 assert sha(D/m['source'])==m['source_sha256']
 rc=json.loads((D/m['receipt']).read_text());assert rc['exit_status']==0 and rc['scope_swap_peak_bytes']==0
 assert rc['object_sha256']==m['object_sha256']
raw=(P/'lean/bridge-prepared-3335-20261016/AspisR1PublicPreparation/Types.lean').read_text()
A=json.loads((D/'naming-adapter.json').read_text());assert hashlib.sha256(raw.encode()).hexdigest()==A['original_sha256']
changes={x['type']:x['constructors'] for x in A['changes']}
pat=r'@\[discriminant isize\]\n(inductive ([\w.]+)[\s\S]*?)(?=\n\n)'
def adapt(m):
 body,name=m.group(1),m.group(2);ct=re.findall(r'^\| (\w+)\s*:\s*([\s\S]*?)(?=^\||\Z)',body,re.M)
 cases=[(n,t.count('→')) for n,t in ct];assert [list(x) for x in cases]==changes[name]
 aux='\n\n-- Naming-only instance qualification; constructor codes unchanged.\n'
 aux+=f'def {name}.read_discriminant (x : {name}) : Isize :=\n  match x with\n'
 aux+=''.join('  | .'+c+' _'*arity+' => '+str(i)+'#isize\n' for i,(c,arity) in enumerate(cases))
 aux+=f'\ninstance _root_.AspisR1PublicPreparation.{name}.instDiscriminant :\n    Aeneas.Std.Discriminant {name} Isize where\n  read_discriminant := {name}.read_discriminant'
 return body+aux
strip=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) [^\n]*\n','',s,flags=re.M)
expected=strip(re.sub(pat,adapt,raw))+'\n#print axioms AspisR1PublicPreparation.verifier.Error.read_discriminant\n'
assert (D/'sources/AspisR1PublicPreparation/Types.lean').read_text()==expected
for f in ['AspisR1PublicPreparation/Funs.lean','ExtractedPreparedModel.lean']:
 assert (D/'sources'/f).read_text()==strip((P/'lean/bridge-prepared-3335-20261016'/f).read_text())
for n in ['CurrentPreparedScratchModel','CurrentPreparedScratchReachability']:
 assert (D/'sources'/(n+'.lean')).read_bytes()==(P/'evidence/s1-current-prepared-extraction-20261020/sources'/(n+'.lean')).read_bytes()
print('PASS: selected green sources/receipts/hashes; exact naming/resource-option adapter; existing caller theorem source unchanged')
