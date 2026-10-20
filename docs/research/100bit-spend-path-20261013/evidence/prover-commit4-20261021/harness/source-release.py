#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R=next(p for p in E.parents if (p/'Cargo.toml').exists())
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
rows=[json.loads(s) for s in (E/'lean/attempts.jsonl').read_text().splitlines()]
commits=subprocess.check_output(['git','rev-list','8c69254eb..HEAD'],cwd=R,text=True).splitlines()
for x in rows:
 rel='docs/research/v8-r0-zk-20261009/lean/'+x['module']
 matches=[]
 for c in commits:
  p=subprocess.run(['git','show',c+':'+rel],cwd=R,capture_output=True)
  if p.returncode==0 and hashlib.sha256(p.stdout).hexdigest()==x['source_sha256']:matches.append(c)
 x['source_revision']=matches[-1] if matches else 'uncommitted rejected draft; exact source SHA recorded'
 assert matches or not x['accepted'], x
(E/'lean/attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in rows))
paths=[R/'crates/aspis-prover/src'/n for n in ['lib.rs','prover_commit_oracle.rs','prover_commit_reference.rs','state_only_entropy.rs','state_only_hiding.rs']]
paths += [p for d in ['R1Z','AspisR1ProverCommitReference'] for p in (R/'docs/research/v8-r0-zk-20261009/lean'/d).glob('*.lean') if d!='R1Z' or p.name in ['ProverCommitOracleRefinement.lean','ProverCommitReferenceSource.lean','ProverCommitOracleAudit.lean','ProverCommitFibreScope.lean']]
(E/'source-release.json').write_text(json.dumps(dict(source_revision=rev,files={str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}),indent=2)+'\n')
