from pathlib import Path
import json,lzma,hashlib,ast,subprocess,re
E=Path(__file__).resolve().parent;sha=lambda x:hashlib.sha256(x).hexdigest()
idx=json.loads((E/'NKF_INPUTS.json').read_text());objects=idx['objects']
for h,x in objects.items():
 p=E/x['path'];raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and sha(p.read_bytes())==x['archive_sha256'] and len(raw)==x['bytes']
for a,inputs in idx['attempts'].items():
 for n,h in inputs.items():assert h in objects
receipts=[json.loads(l) for l in (E/'NKF_ATTEMPTS.jsonl').read_text().splitlines()]
for r in receipts:
 a=r['attempt'];assert json.loads((E/a/'receipt.json').read_text())==r
 ad=json.loads((E/(a+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for n,h in r['source_hashes'].items():assert idx['attempts'][a][n]==h
 if r['kind']=='kani' and a!='NKF_K001':
  g=json.loads((E/(a+'-graph-check.json')).read_text());l=json.loads((E/(a+'-lock-check.json')).read_text());s=json.loads((E/(a+'-erasure-check.json')).read_text())
  assert g['graph_matches_frozen'] and g['all_features'] and l['unchanged'] and s['passed']
for p in E.rglob('*.log.xz'):
 raw=lzma.decompress(p.read_bytes());assert sha(raw)==p.with_name(p.name[:-3]+'.sha256').read_text().strip()
for p in E.glob('*.py'):ast.parse(p.read_text())
for p in E.glob('NKF_*.lean'):
 s=p.read_text();assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\bnative_decide\b|set_option max(?:Heartbeats|RecDepth)',s,re.M)
 for name in re.findall(r'^theorem (\w+)',s,re.M):assert '#print axioms '+name in s,(p,name)
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
assert not list(E.glob('*.rs'))
assert not json.loads((E/'NKF_CLOSED.json').read_text())['functions']
assert json.loads((E/'NKF_LEDGER_DELTA.json').read_text())['changes']==[]
assert json.loads((E/'NKF_AUDIT.json').read_text())['combined_audits_run']==0
assert not (E/'NKF_K081/receipt.json').exists()
assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs','Cargo.lock']).returncode==0
out=dict(status='PASS_LOCAL_EVIDENCE_INTEGRITY_ONLY',input_objects=len(objects),attempt_inputs=len(idx['attempts']),receipts=len(receipts),frozen_source_unchanged=True,no_file_over20MiB=True,no_row_promotion=True,host_gate_not_run=True)
(E/'NKF_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
