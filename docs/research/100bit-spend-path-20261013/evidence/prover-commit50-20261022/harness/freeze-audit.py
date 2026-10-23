"""Freeze the exact accepted local targets before the one final focused audit."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
base=(E/'pins/revision.txt').read_text().strip()
records=json.loads((E/'lean/attempts.json').read_text())
paths=sorted(list((L/'R1Z').glob('ProverCommit*50.lean'))+list((L/'AspisR1ProducerRelease47').glob('*50.lean')))
paths=[p for p in paths if p.name!='ProverCommitAudit50.lean']
mods=[];theorems=[];private=[];frozen=[]
for p in paths:
 s=p.read_text();m=str(p.relative_to(L))[:-5].replace('/','.')
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 accepted=[r for r in records if r['module']==str(p.relative_to(L)) and r['source_sha256']==sha and r['exit_status']==['0']]
 assert accepted,('No accepted current target',m,sha)
 ns=re.findall(r'^namespace (\S+)',s,re.M)
 assert len(set(ns))==1,(m,ns)
 for mat in re.finditer(r'^(?:@\[[^\n]+\]\s*)?(?:(private)\s+)?(?:theorem|lemma)\s+([^\s({:]+)',s,re.M):
  name=ns[0]+'.'+mat[2]
  (private if mat[1] else theorems).append(name)
 mods.append(m)
 frozen.append(dict(module=m,source=str(p),sha256=sha,accepted_attempt=accepted[-1]['attempt'],deps_fingerprint=accepted[-1]['deps_fingerprint']))
endpoint=L/'R1Z/ProverCommitDeployedFuel22.lean'
assert endpoint.read_bytes()==(E/'endpoint/before.lean.txt').read_bytes()==(E/'endpoint/after.lean.txt').read_bytes()
text='import R1Z.ProverCommitAudit49\n'+''.join('import '+m+'\n' for m in mods)+'import R1Z.ProverCommitDeployedFuel22\n'
text+='/-! One coherent import/axioms audit of the accepted part-50 cone.\nNo complete simulator payload or frozen-manifest release claim is made. -/\n'
text+=''.join('#print axioms '+t+'\n' for t in theorems)
text+='#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed\n'
p=L/'R1Z/ProverCommitAudit50.lean';p.write_text(text)
(E/'pins/final-lean-freeze.json').write_text(json.dumps(dict(task_base_revision=base,audit_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),modules=frozen,public_theorems=theorems,private_theorems_audited_in_original_targets=private,endpoint_sha256=hashlib.sha256(endpoint.read_bytes()).hexdigest()),indent=2)+'\n')
subprocess.run(['git','diff','--exit-code',base,'--','crates','programs'],check=True)
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','crates','programs'],text=True).splitlines();assert not new,new
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base,'--','crates','programs'],text=True).splitlines()
inv=[]
for name in files:
 p=Path(name)
 data=p.read_bytes()
 inv.append(dict(path=name,sha256=hashlib.sha256(data).hexdigest(),size=len(data)))
(E/'pins/final-shipped-inventory.json').write_text(json.dumps(dict(base_revision=base,unchanged_by_git_diff=True,new_untracked_files=new,file_count=len(inv),files=inv,elf_rebuild_triggered=False,retained_user_release_pins=dict(default='40dc7574...',devnet='12cb0bc2...',pool='121f3e29...'),qualification='No crates/ or programs/ file changed in this task. No fresh ELF identity claim; prior frozen pins retained.'),indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),public_theorems=len(theorems),private_theorems=len(private),shipped_files=len(inv),audit_sha256=hashlib.sha256((L/'R1Z/ProverCommitAudit50.lean').read_bytes()).hexdigest())))
