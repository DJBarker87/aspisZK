#!/usr/bin/env python3
"""Summarize final gates without repeating them. Run after the retry gate ends."""
import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]); OLD=Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((H/'source-hashes.json').read_text())
for f,v in manifest['files'].items():assert sha(H/'src'/f)==v,f
codec=H/'receipts/gate-codec-1233/stdout.log'
assert sha(codec)=='3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321'
assert codec.read_text().splitlines()[-1]=='complete 1233'
summary=dict(source_revision='731018bdc',source_hashes_checked=len(manifest['files']),codec=dict(outputs=1233,sha256=sha(codec),bytes=codec.stat().st_size))
for label,base in [('audit-eight-way',Path('/home/dombarker/project-offloads/codex-r1p-writer-migration-20261019/out/ordered-counter-new.json')),('adopted',OLD/'runs/counter-adopted.json')]:
 a=json.loads((H/f'runs/counter-{label}.json').read_text()); b=json.loads(base.read_text())
 for r in [a,b]:r['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda x:x['input_hex'])
 for k in ['ordered_digest_calls','hash_input_counts','acceptance']:assert a[k]==b[k],(label,k)
 summary['ordered_'+label]=dict(calls=len(a['ordered_digest_calls']),ordered_calls_counts_acceptance_equal=True,baseline=str(base),baseline_sha256=sha(base))
b1={'transfer-13':(1199648,1129757),'transfer-255':(1199567,1161066),'transfer-1023':(1199687,1160974),'withdrawal-13':(1198225,1138950),'withdrawal-255':(1198264,1170523),'withdrawal-1023':(1198386,1170263)}
rows=[]
identity=json.loads((H/'receipts/identity/identity.json').read_text())
for l,(s,t) in b1.items():
 p=H/f'runs/default/{l}/evidence.json'; j=json.loads(p.read_text());e=j['execution']
 assert e['outcome']=='accepted' and e['error'] is None
 assert j['artifacts']['r1_cost_probe_verifier']['sha256']==identity['artifacts']['default']['sha256']
 assert e['stage1_compute_units']<=s and e['compute_units']<=t+10000
 rows.append(dict(fixture=l,stage1_cu=e['stage1_compute_units'],settlement_cu=e['compute_units'],b1_stage1=s,b1_settlement=t,stage1_delta=e['stage1_compute_units']-s,settlement_delta=e['compute_units']-t,evidence_sha256=sha(p),proof_sha256=sha(H/f'runs/adopt/{l}/task/r1-s2-proof.bin'),public_sha256=sha(H/f'runs/adopt/{l}/task/r1-s2-public-asf8.bin')))
summary['cu']=rows
for k in ['pool','verifier']:assert json.loads((H/f'stack/{k}/stack-audit.json').read_text())['gate_pass']
r=json.loads((H/'runs/r1p-retry-gate.json').read_text());assert r['attempts']>=8 and r['accepted']>=8 and r['accepted_proofs_verified_strict_and_dense']>=8
assert r['retry_loop']['verified_strict_and_dense']
summary['retry']=r
receipts=[]
for p in sorted((H/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0,p
 receipts.append(dict(run=p.parent.name,**r))
summary['receipts']=receipts
summary['print_axioms']='N/A: Rust/SBF only'
(H/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
pins=[]
for k in ['default','devnet','pool']:
 for p in sorted((H/'artifacts'/k).glob('*')):
  if p.suffix in ['.so','.elf']:pins.append(f'{sha(p)}  {p.stat().st_size} bytes  {p.relative_to(H)}')
for p in [OLD/'artifacts/pool_gate_adopt',Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so')]:pins.append(f'{sha(p)}  {p.stat().st_size} bytes  {p}')
(H/'artifacts-sha256.txt').write_text('\n'.join(pins)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['retry','receipts']},indent=2))
