#!/usr/bin/env python3
"""Check adopted receipt status, trust boundary and exact source identities."""
from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
accepted_rust=[
 'mask-next-no-panic-v3','source-next-no-panic-v1',
 'mask-next-no-formatter-v1','source-next-no-formatter-v1',
 'transcript-query-caller-v2','mask-scalar-partition-v1',
]
extra=E/'accepted-extra.json'
if extra.exists():accepted_rust+=json.loads(extra.read_text())
# Source snapshots can differ only by exact retained proof-only additions.
known={}
for d in E.parent.glob('prover-commit*'):
 for folder in [d/'rust-sources',d/'harness']:
  if not folder.exists():continue
  for p in folder.rglob('*'):
   if p.is_file() and p.stat().st_size<5_000_000:
    known.setdefault(hashlib.sha256(p.read_bytes()).hexdigest(),str(p))
checks=[]
for name in accepted_rust:
 r=json.loads((E/'receipts'/name/'receipt.json').read_text())
 assert r['exit_status']==0,(name,r)
 assert r['swaps']==0,name
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},name
 assert r['env']['RUSTFLAGS']=='-C link-arg=-Wl,--threads=4',name
 out=(E/'receipts'/name/'stdout.log').read_text()
 assert 'VERIFICATION:- SUCCESSFUL' in out,name
 assert '--unwinding-assertions' in r['command'],name
 x=json.loads((E/(name+'-inputs.json')).read_text())
 unresolved=[]
 for path,sha in x['source_hashes'].items():
  p=Path(path)
  if p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==sha:continue
  if sha in known:continue
  unresolved.append((path,sha))
 assert not unresolved,(name,unresolved)
 checks.append(dict(name=name,status='accepted',source_count=len(x['source_hashes']),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_peak=r['cgroup_memory_peak_bytes']))
lean_rows={r["attempt"]:r for p in (E/"lean").glob("attempts-*.jsonl") for line in p.read_text().splitlines() if (r:=json.loads(line))}
for attempt in [8365,8367,8368,8369,8370,8371,8372]:
 x=lean_rows[attempt]
 assert x['exit_status']==0 and x['swaps']==0,attempt
 for line in x['axioms']:
  assert 'sorryAx' not in line and 'Formatter' not in line,(attempt,line)
  m=re.search(r'axioms: \[([^]]*)\]',line,re.S)
  if m:assert set(re.split(r',\s*',m[1].strip()))<={'propext','Quot.sound','Classical.choice'},(attempt,line)
 snap=next((E/'lean/sources').glob(f'attempt-{attempt}-*.lean.txt'))
 assert hashlib.sha256(snap.read_bytes()).hexdigest()==x['source_sha256'],attempt
full_inputs=json.loads((E/'final-source-inputs.json').read_text())
for name,sha in full_inputs.items():
 p=Path(name)
 assert (p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==sha) or sha in known,(name,sha)
checks.append(dict(full_rust_input_snapshot=len(full_inputs),exact_identity='baseline or retained literal proof-only source'))
checks.append(dict(headline_diff='one binder deleted after explicit specialization',source_base='9f6852af9'))
before=(E/'headline-specialized-before.lean.txt').read_text()
after=(E/'headline-specialized-after.lean.txt').read_text()
assert before.replace('    (builder_premises : BuilderPremises h B x)\n','')==after
assert (E/'headline-original.lean.txt').read_text()==Path('docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineOwnedClosed.lean').read_text()
assert after==Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitAdmittedEndpoint.lean').read_text()
assert not subprocess.check_output(['git','diff','--name-only','9f6852af9','--','crates','programs','Cargo.toml','Cargo.lock'],text=True).strip()
(E/'validation.json').write_text(json.dumps(checks,indent=2)+'\n')
print('Validated',len(accepted_rust),'Rust certificates and focused Lean audits; no full-shipped claim.')
