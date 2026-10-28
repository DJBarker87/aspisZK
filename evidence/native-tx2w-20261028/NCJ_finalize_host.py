from NCJ_host import *
import sys
# Run only after this lane's final proof receipt; no prover submission here.
imports=json.loads((E/'NCJ_IMPORTED_CACHE.json').read_text());frozen=json.loads((E/'NCJ_FROZEN_SOURCES.json').read_text())
r=py(f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-tx2weights-cache-20261028')
imports=json.loads({json.dumps(json.dumps(imports))});chosen={{r['relative']:r for r in imports}};changed=[]
for rel,row in chosen.items():
 p=cache/rel
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=row['sha256']:changed.append(rel)
frozen=json.loads({json.dumps(json.dumps(frozen))});diff=[]
for rel,h in frozen.items():
 p=b/'NCJ_src'/rel
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=h:diff.append(rel)
new=[str(p.relative_to(b/'NCJ_src')) for p in (b/'NCJ_src').rglob('*') if p.is_file() and str(p.relative_to(b/'NCJ_src')) not in frozen]
print(json.dumps(dict(imported_unique=len(chosen),imported_changed=changed,frozen_changed=diff,new_files=new,cache_retained=str(cache)),indent=2))
''');assert r.returncode==0,r.stderr
result=json.loads(r.stdout);assert result['imported_changed']==[]
allowed=['crates/aspis-r1-cost-probe/src/'+n for n in ['lib.rs','weights.rs','verifier.rs','fast_pairing.rs']]
assert sorted(result['frozen_changed'])==sorted(allowed),result['frozen_changed']
(E/'NCJ_FINAL_HOST.json').write_text(json.dumps(result,indent=2)+'\n')
print('Imported cache unchanged; frozen source differences confined to four scratch cfg harness insertions')
