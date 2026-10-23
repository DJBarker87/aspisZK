#!/usr/bin/env python3
"""Audit direct actual SDK/model bounded coupling and unchanged unary-frame sources."""
from pathlib import Path
import hashlib,json,tempfile,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';E=B/'sdk-live-pairs';U=B/'sdk-live-contracts'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
for n,d in load(E/'manifest.json')['files'].items():assert sha(E/n)==d,n
assert not any(p.suffix in ['.out','.rlib','.o','.llbc'] for p in E.rglob('*'))
assert sha(E/'original-sdk/src/lib.rs')==sha(U/'original-sdk/src/lib.rs')=='6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a'
accepted=[]
for mode,n in [('length',707),('shared',811),('exclusive',811)]:
 P=E/'sources'/mode;tag=f'sdk-live-pair-{mode}-check-v1';inp=load(E/(tag+'-input.json'));r=load(E/'receipts'/tag/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
 assert inp['source_sha256']==sha(P/'src/lib.rs') and inp['crate_source_pins']['src/sdk_live_models.rs']==sha(P/'src/sdk_live_models.rs')
 log=(E/'receipts'/tag/'stdout.log').read_text();assert f'0 of {n} failed' in log and '3 of 3 cover properties satisfied' in log
 rows=[x for x in load(E/'metadata'/mode/'harness-metadata.json')['proof_harnesses'] if x['pretty_name']=='proofs::actual_sdk_live_contract'];assert len(rows)==1
 assert rows[0]['attributes']['kind']=='Proof' and not rows[0]['attributes']['stubs'] and not rows[0]['attributes']['verified_stubs']
 C=U/'sources'/f'sdk-live-model-contract-{mode}-v2';cut=load(C/'source-cut.json')
 assert (C/'src/sdk_live_models.rs').read_text().replace(cut['model_contract_annotation'],'')==(P/'src/sdk_live_models.rs').read_text()
 assert load(E/(tag+'-dependency-postcheck.json'))['unchanged']=={}
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'pair';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-live-pair-ordinary.py'),str(out),mode],check=True)
  for rel in ['src/lib.rs','src/sdk_live_models.rs','Cargo.toml','source-cut.json']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),rel
 accepted.append(dict(target=tag,checks=n,covers=3,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axioms='N/A bounded Kani; no Lean theorem'))
print(json.dumps(dict(accepted=accepted,qualification='Direct ordinary result/live-guard/counter/Drop-restoration pairs. Existing matching actual/model unary whole-heap frames reused; contextual/runtime/ABI and complete enclosing source/caller joins remain.'),indent=2))
