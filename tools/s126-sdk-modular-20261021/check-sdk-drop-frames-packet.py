#!/usr/bin/env python3
"""Source-only counter-frame audit for actual original std guards."""
from pathlib import Path
import hashlib,json,tempfile,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-drop-frames'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
for n,d in load(E/'manifest.json')['files'].items():assert sha(E/n)==d,n
assert not any(p.suffix in ['.out','.rlib','.o','.llbc'] for p in E.rglob('*'))
accepted=[]
for mode,n in [('shared',760),('exclusive',740)]:
 P=E/'sources'/mode;tag=f'sdk-drop-{mode}-frame-v1';i=load(E/(tag+'-input.json'));r=load(E/'receipts'/tag/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
 assert i['source_sha256']==sha(P/'src/lib.rs')
 log=(E/'receipts'/tag/'stdout.log').read_text();assert f'0 of {n} failed' in log and '3 of 3 cover properties satisfied' in log
 rows=[x for x in load(E/'metadata'/mode/'harness-metadata.json')['proof_harnesses'] if x['pretty_name']=='proofs::actual_sdk_live_contract'];assert len(rows)==1
 assert rows[0]['attributes']['kind']=={'ProofForContract':{'target_fn':'finish_guard'}} and not rows[0]['attributes']['stubs'] and rows[0]['contract']
 assert not rows[0]['attributes']['verified_stubs'] and '--unwinding-assertions' in i['command']
 assert '-C opt-level=3' in i['env']['RUSTFLAGS']
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'drop';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-drop-frame.py'),str(out),mode],check=True)
  for rel in ['src/lib.rs','Cargo.toml','source-cut.json']:assert (out/rel).read_bytes()==(P/rel).read_bytes()
 accepted.append(dict(target=tag,checks=n,covers=3,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axioms='N/A bounded Kani contract'))
print(json.dumps(dict(accepted=accepted,qualification='Actual live typed guard Drop counter-only frame and exact decrement/reset. Matching acquisition preconditions, runtime/ABI and enclosing source/caller composition remain.'),indent=2))
