"""Verify the reused host's actual native/release source inputs against HEAD."""
from pathlib import Path
import json,subprocess
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
roots=['Cargo.toml','Cargo.lock','crates','programs','xtask','audit','tools/r1-cost-probe','tools/prover-rw-20261023','docs/research/v8-r0-zk-20261009/c3/check/src/native_workers.rs']
raw=subprocess.check_output(['git','ls-tree','-rz',rev,'--',*roots])
rows=[]
for item in raw.split(b'\0'):
 if not item:continue
 meta,path=item.split(b'\t',1);mode,kind,blob=meta.decode().split()
 if kind=='blob':rows.append(dict(path=path.decode(),blob=blob,mode=mode))
code='''from pathlib import Path
import hashlib,json,os
S=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027/candidate/src')
rows=ROWS
for r in rows:
 p=S/r['path']
 if not p.exists():r.update(matches=False,error='missing');continue
 b=os.readlink(p).encode() if p.is_symlink() else p.read_bytes()
 h=hashlib.sha1(('blob '+str(len(b))+'\\0').encode()+b).hexdigest()
 r.update(actual_blob=h,bytes=len(b),matches=h==r['blob'])
print(json.dumps(rows))
'''.replace('ROWS',repr(rows))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True)
rows=json.loads(r.stdout);bad=[r for r in rows if not r['matches']]
out=dict(source_revision=rev,scope=roots,files=rows,mismatches=bad,passed=not bad,print_axioms='N/A read-only source identity')
p=Path('evidence/pv-batch2-20261027/batch2f/SOURCE-IDENTITY.json');p.write_text(json.dumps(out,indent=2)+'\n')
assert not bad,bad
print('verified',len(rows),'native/release source inputs')
