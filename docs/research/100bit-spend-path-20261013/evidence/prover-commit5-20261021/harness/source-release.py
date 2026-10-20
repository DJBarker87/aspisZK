#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R=next(p for p in E.parents if (p/'Cargo.toml').exists())
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(s) for s in (E/'lean/attempts.jsonl').read_text().splitlines()]
commits=subprocess.check_output(['git','rev-list','--reverse','a7b7621d9..HEAD'],cwd=R,text=True).splitlines()
for x in rows:
 rel='docs/research/v8-r0-zk-20261009/lean/'+x['module']
 matches=[]
 for c in commits:
  p=subprocess.run(['git','show',c+':'+rel],cwd=R,capture_output=True)
  if p.returncode==0 and hashlib.sha256(p.stdout).hexdigest()==x['source_sha256']:matches.append(c)
 if matches: x['source_revision']=matches[0]
 else:
  assert not x['accepted'],x
  snap=E/'lean/rejected-sources'/f"{x['attempt']}.lean"
  assert snap.exists() and sha(snap)==x['source_sha256'],x['attempt']
  x['source_revision']='a7b7621d9 plus exact rejected working-tree snapshot'
  x['source_snapshot']=str(snap.relative_to(R))
(E/'lean/attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
paths=[R/'crates/aspis-prover/src'/n for n in ['lib.rs','prover_commit_oracle.rs','prover_commit_reference.rs','state_only_entropy.rs','state_only_hiding.rs']]
paths += [R/('docs/research/v8-r0-zk-20261009/lean/'+x['module']) for x in rows if x['accepted']]
pins={str(p.relative_to(R)):sha(p) for p in paths}
(E/'source-release.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),base_revision='a7b7621d9',files=pins),indent=2)+'\n')
