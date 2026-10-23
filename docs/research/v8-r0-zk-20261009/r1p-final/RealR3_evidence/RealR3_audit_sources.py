"""Read-only current/frozen source and accepted-theorem integrity audit."""
from pathlib import Path
import hashlib,json,subprocess,re
E=Path(__file__).resolve().parent;R=E.parents[4]
base='1bffe648cad26e07572e4e2e7ac2d4b33795a7de'
shipped=subprocess.check_output(['git','ls-files','crates','programs'],cwd=R,text=True).splitlines()
changes=[]
for p in shipped:
 before=subprocess.check_output(['git','show',base+':'+p],cwd=R)
 if (R/p).read_bytes()!=before:changes.append(p)
assert not changes,changes
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard','crates','programs'],cwd=R,text=True).splitlines();assert not untracked
files=[R/'docs/research/v8-r0-zk-20261009/lean/R1Z'/p for p in ['RealR3_SemanticEmission.lean','RealR3_EmissionPrefix.lean']]
for p in files:
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s)
 assert 'maxRecDepth' not in s and 'maxHeartbeats' not in s
 assert len(re.findall(r'^theorem ',s,re.M))==len(re.findall(r'^#print axioms ',s,re.M))
field={}
for f in ['field.rs','field/wide_exact.rs']:
 p=R/'crates/aspis-core/src'/f;q=E/'RealR3_native'/f
 assert p.read_bytes()==q.read_bytes();field[f]=hashlib.sha256(p.read_bytes()).hexdigest()
# Compare actual relevant transcript/validator methods with the part-28 source.
w=(R/'crates/aspis-r1-cost-probe/src/r1_wire.rs').read_text()
old=subprocess.check_output(['git','show','f53e30fc4e26375c1bd0623532dafaf49571dc9d:crates/aspis-r1-cost-probe/src/r1_wire.rs'],cwd=R,text=True)
def item(s,n):
 a=s.index(n);b=s.index('{',a);d=1;i=b+1
 while d:
  if s[i]=='{':d+=1
  elif s[i]=='}':d-=1
  i+=1
 return s[a:i]
spans={}
for n in ['pub fn new(hash:', 'fn sample_block_validated(', 'fn sample_block(', 'pub fn semantic(&mut self']:
 x=item(w,n);assert x==item(old,n),n;spans[n]=hashlib.sha256(x.encode()).hexdigest()
out={'base':base,'shipped_tracked_files':len(shipped),'shipped_changes':changes,'untracked_shipped_files':untracked,'field_source_identity':field,'part28_exact_method_identity':spans,'new_lean_sources':{str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'claim':'source integrity only; native/model bridge still requires its gate','ELF_rebuild':'not triggered: no shipped-file change'}
(E/'RealR3_source-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
