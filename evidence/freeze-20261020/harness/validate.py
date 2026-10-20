#!/usr/bin/env python3
"""Read-only final evidence validation; does not rerun any build or gate."""
from pathlib import Path
import json,hashlib,re
H=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert (H/'ALL-PASS').exists()
manifest=json.loads((H/'source-hashes.json').read_text())
for f,v in manifest['files'].items():assert sha(H/'src'/f)==v,f
identity=json.loads((H/'receipts/identity/identity.json').read_text());assert identity['text_identical'] and identity['only_two_data_slots']
r=json.loads((H/'runs/r1p-retry-gate.json').read_text());assert r['attempts']>=8 and r['accepted']>=8 and r['accepted_proofs_verified_strict_and_dense']>=8
assert r['retry_loop']['verified_strict_and_dense']
sim=json.loads((H/'runs/simulator.json').read_text());assert len(sim['runs'])==4
for r in sim['runs']:
 assert r['verified_strict_and_dense_under_programmed_oracle'] and r['real_hash_strict_rejected'] and r['real_hash_dense_rejected']
 assert r['programmed_addresses']==r['programmed_addresses_read_by_verifier']
for p in (H/'receipts').glob('*/receipt.json'):
 r=json.loads(p.read_text());assert r['exit_status']==0,p
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0',p
for mode in ['default','devnet','pool']:assert json.loads((H/'stack'/mode/'stack-audit.json').read_text())['gate_pass']
codec=H/'receipts/gate-codec-1233/stdout.log';assert sha(codec)=='3ef16b12a329dd6d74b472cd75e5554c1ef8d98c618de3117f87b6c50d73e321' and codec.read_text().splitlines()[-1]=='complete 1233'
traces=[]
for name,base in [('adopted',Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/runs/counter-adopted.json')),('audit-eight-way',Path('/home/dombarker/project-offloads/codex-r1p-writer-migration-20261019/out/ordered-counter-new.json'))]:
 p=H/f'runs/counter-{name}.json';a=json.loads(p.read_text());b=json.loads(base.read_text())
 for x in [a,b]:x['hash_input_counts']['repeated_exact_inputs'].sort(key=lambda y:y['input_hex'])
 for k in ['ordered_digest_calls','hash_input_counts','acceptance']:assert a[k]==b[k],(name,k)
 traces.append(dict(name=name,calls=len(a['ordered_digest_calls']),sha256=sha(p),baseline=str(base),baseline_sha256=sha(base),ordered_calls_counts_acceptance_equal=True))
# Keep all fixture evidence and assertions about exact measured artifact.
for row in json.loads((H/'cu.json').read_text()):
 assert row['stage1_margin']>=0 and row['settlement_margin']>=0 and row['outcome']=='accepted'
 j=json.loads((H/'runs/cu'/row['fixture']/'evidence.json').read_text());assert j['artifacts']['r1_cost_probe_verifier']['sha256']==identity['artifacts']['default']['sha256']
pins=[]
for p in sorted((H/'artifacts').glob('*/*')):
 if p.suffix in ['.so','.elf']:pins.append(p)
pins.extend([H/'extraction-freeze/Stage2.llbc',Path('/home/dombarker/project-offloads/active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so'),Path('/home/dombarker/project-offloads/codex-r1-format-adopt-20261019/artifacts/pool_gate_adopt')])
assert sha(H/'artifacts/pool/aspis_pool.so')=='121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'
(H/'artifacts-sha256.txt').write_text(''.join(f'{sha(p)}  {p.stat().st_size} bytes  {p}\n' for p in pins))
(H/'validation.json').write_text(json.dumps(dict(source_revision=manifest['source_revision'],source_files_checked=len(manifest['files']),codec_outputs=1233,codec_sha256=sha(codec),traces=traces,all_command_receipts_zero_exit=True,all_gate_swaps_zero=True,print_axioms='N/A: Rust/SBF only'),indent=2)+'\n')
print('PASS: all final evidence assertions')
