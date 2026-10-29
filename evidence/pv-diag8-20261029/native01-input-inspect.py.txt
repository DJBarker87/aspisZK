from pathlib import Path
import json,lzma,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029'); P=D.parent/'codex-pv-diag-20261029'; R=D.parent/'codex-pv-rdea-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]; logs=[]
for p in sorted(P.glob('shard-*.json.xz')):
 with lzma.open(p,'rt') as f:x=json.load(f)
 for r in x['sites']:
  if 'log_candidate' in r['classes']:logs.append(r)
  if r['kind']=='mir' and any(k in r['function'] for k in ['prover::','plan::','Client64','next_word','Accounts','publication','round(']):rows.append(r)
(D/'selected-ir-sites.json').write_text(json.dumps(rows,indent=2)+'\n')
(D/'logger-ir-sites.json').write_text(json.dumps(logs,indent=2)+'\n')
print('selected',len(rows),'log candidates',len(logs))
for p in sorted(R.glob('*graph*')):
 print(p.name)
 with lzma.open(p,'rt') as f:x=json.load(f)
 print(list(x)[:15]);print(str(x)[:500])
root=D.parent/'codex-pv-fscan-20261028/src'
for rel in ['crates/aspis-r1-cost-probe/src/prover.rs','crates/aspis-prover/src/state_only_entropy.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs']:
 p=root/rel;print(rel,sha(p))
