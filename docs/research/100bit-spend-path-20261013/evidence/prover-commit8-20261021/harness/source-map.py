#!/usr/bin/env python3
"""Reconstruct excluded/earlier literal proof configurations and verify hashes."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
R=Path('crates/aspis-prover/src')
variants={}
final={n:(R/n).read_text() for n in ['prover_commit_reference.rs','state_only_hiding.rs','state_only_entropy.rs']}
variants['adopted-step-stage']=final
variants['scalar-step-v1']={
 'prover_commit_reference.rs':final['prover_commit_reference.rs'].split('\n/// One row of the owned balancing fold.')[0],
 **{n:subprocess.check_output(['git','show','a9a27745b:'+str(R/n)],text=True) for n in ['state_only_hiding.rs','state_only_entropy.rs']}}
pre={}
for n in ['state_only_hiding.rs','state_only_entropy.rs']:
 s=final[n];at=s.index('mod prover_commit_four8')
 s=s[:at]+s[at:].replace('#[kani::unwind(34)]','#[kani::unwind(5)]')
 if n=='state_only_hiding.rs':
  at=s.index('mod prover_commit_balance8');end=s.index('/// Universal four-call',at)
  s=s[:at]+s[at:end].replace('#[kani::unwind(34)]','#[kani::unwind(3)]')+s[end:]
 pre[n]=s
variants['mask-four-trace-v2']={**final,**pre}
s=pre['state_only_entropy.rs'];at=s.index('mod prover_commit_four8');s=s[:at]+s[at:].replace('*state.seed = after.seed','state.seed = after.seed').replace('seed: Zeroizing::new(state.seed), counter:', 'seed: state.seed, counter:').replace('assert_eq!(*actual.seed, after.seed)','assert_eq!(actual.seed, after.seed)')
variants['mask-four-trace-v1']={**final,**pre,'state_only_entropy.rs':s}
for label,files in variants.items():
 for name,body in files.items():
  p=E/'rust-sources'/label/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(body)
rows=[]
for p in sorted(E.glob('*-inputs.json')):
 x=json.loads(p.read_text())
 for rel,sha in x.get('source_hashes',{}).items():
  candidates=[Path(rel)]
  if Path(rel).parent==R:candidates += list((E/'rust-sources').glob('*/'+Path(rel).name))
  match=next((c for c in candidates if c.exists() and hashlib.sha256(c.read_bytes()).hexdigest()==sha),None)
  assert match,(p.name,rel,sha)
  rows.append(dict(inputs=str(p.relative_to(E)),source=rel,sha256=sha,matching_file=str(match)))
(E/'rust-source-map.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Verified',len(rows),'Rust source identities')
