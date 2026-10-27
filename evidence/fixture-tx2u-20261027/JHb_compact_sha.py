"""Move existing SHA transition intermediates to paired global tuple definitions.
Exact same input/start/result and 64 transition equations; no new hash leaf.
This reduces imported global environment size after JHb_TX2_021 memory failure.
"""
from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
mapping={f'JGz_SHAP{i:02}':f'JHb_SHAP{i:02}' for i in range(28)}
mapping.update({f'JGz_ProofNative{i:02}':f'JHb_ProofNative{i:02}' for i in range(7)})
mapping.update(JGz_ProofSHA='JHb_ProofSHA',JGz_Realizes='JHb_Realizes',JGz_ProofDigest='JHb_ProofDigest')
def rename(s):
 for a,b in mapping.items():s=s.replace(a,b)
 return s
files={};manifest={}
for i in range(28):
 old=f'JGz_SHAP{i:02}';s=(R/'lean'/(old+'.lean')).read_text()
 def compact(m):
  name=m[1];body=m[2]
  inp=re.search(r'^def input.*$',body,re.M)[0];start=re.search(r'^def start.*$',body,re.M)[0];result=re.search(r'^def result.*$',body,re.M)[0]
  w={int(k):v for k,v in re.findall(r'^def w(\d+) : List Nat := (.*)$',body,re.M)}
  states={int(k):v for k,v in re.findall(r'^def s(\d+) : Reg := (.*)$',body,re.M)}
  assert len(w)==len(states)==65
  constants=re.findall(r'have t\d+ : transition \(w\d+,s\d+\) (\d+)=',body)
  assert len(constants)==64
  out=[f'namespace {name}',inp,start,result]
  out += [f'def q{j:02} : List Nat × Reg := ({w[j]},{states[j]})' for j in range(65)]
  out += ['theorem checked : compress start (words input)=result := by','  have parsed : words input=q00.1 := by rfl','  unfold compress loop','  rw [parsed]','  change add start (constants.foldl transition q00).2=result']
  out += [f'  have t{j:02} : transition q{j:02} {k}=q{j+1:02} := by rfl' for j,k in enumerate(constants)]
  out += ['  unfold constants']+[f'  rw [List.foldl_cons,t{j:02}]' for j in range(64)]+['  rw [List.foldl_nil]','  rfl','#print axioms checked',f'end {name}']
  return '\n'.join(out)
 converted=re.sub(r'namespace (B\d+)\n(.*?)end \1',compact,s,flags=re.S)
 assert converted.count('theorem checked')==16
 files[mapping[old]]=rename(converted)
 manifest[old]=dict(source_sha256=hashlib.sha256(s.encode()).hexdigest(),blocks=16,global_intermediates_removed=1040)
for old,new in mapping.items():
 if old.startswith('JGz_SHAP') or old=='JGz_ProofDigest':continue
 files[new]=rename((R/'lean'/(old+'.lean')).read_text())
for name,s in files.items():
 p=R/'lean'/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
s=json.dumps(manifest,indent=2)+'\n'
if '--check' in sys.argv:assert (P/'JHb_COMPACT.json').read_text()==s
else:(P/'JHb_COMPACT.json').write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(files),'modules;448 same blocks;29120 fewer global intermediate definitions')
