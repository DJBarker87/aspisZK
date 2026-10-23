#!/usr/bin/env python3
"""Validate combined real-guard frame evidence and source identity."""
from pathlib import Path
import json,hashlib,tempfile,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-drop-chain'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc'] for p in E.rglob('*'))
q=load(E/'qualification.json');tag='sdk-native-drop-chain-check-v3';r=load(E/'receipts'/tag/'receipt.json');i=load(E/(tag+'-input.json'));P=E/'sources/3'
assert r==q['targets'][tag]['receipt'] and r['exit_status']==0 and r['swaps']==0
assert int(r['limits']['memory.max'])==8*1024**3 and r['limits']['memory.swap.max']=='0'
assert sha(P/'src/lib.rs')==i['source_sha256']==q['targets'][tag]['source_sha256']
assert '-C opt-level=3' in i['env']['RUSTFLAGS'] and '--unwinding-assertions' in i['command']
log=(E/'receipts'/tag/'stdout.log').read_text();assert '0 of 1632 failed' in log and '2 of 2 cover properties satisfied' in log
h=[h for h in load(E/'metadata/harness-metadata.json')['proof_harnesses'] if h['pretty_name']=='proofs::actual_sdk_drop_chain'];assert len(h)==1;h=h[0]
assert h['attributes']['kind']=={'ProofForContract':{'target_fn':'native_drop_chain'}} and h['contract']
assert not h['attributes']['stubs'] and not h['attributes']['verified_stubs'] and h['attributes']['unwind_value']==33
assert all(load(E/(tag+'-dependency-postcheck.json'))['unchanged'].values())
for package,pin in i['local_dependency_source_pins'].items():
 for rel,d in pin['files'].items():assert sha(E/'dependencies'/package/rel)==d
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'cut';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-drop-chain.py'),str(out)],check=True)
 for rel in ['src/lib.rs','Cargo.toml','source-cut.json']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),rel
print(json.dumps(dict(target=tag,checks=1632,covers=2,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axioms='N/A bounded Kani frame contract',scope=q['scope']),indent=2))
