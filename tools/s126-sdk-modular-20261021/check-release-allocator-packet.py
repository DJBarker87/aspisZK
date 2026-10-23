#!/usr/bin/env python3
"""Check release allocator candidate receipts; no solver replay or dispatch claim."""
from pathlib import Path
import json,hashlib,tempfile,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-release-allocator'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc'] for p in E.rglob('*'))
q=load(E/'qualification.json');assert len(q['accepted'])==3
for tag,row in q['accepted'].items():
 P=E/'sources'/row['source'];r=load(E/'receipts'/tag/'receipt.json');i=load(E/(tag+'-input.json'));log=(E/'receipts'/tag/'stdout.log').read_text()
 assert r['exit_status']==0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
 assert sha(P/'src/lib.rs')==i['source_sha256']==row['source_sha256']
 assert f"0 of {row['checks']} failed" in log and f"{row['covers']} of {row['covers']} cover properties satisfied" in log
 assert '-C opt-level=3' in i['env']['RUSTFLAGS'] and '--unwinding-assertions' in i['command']
 assert all(load(E/(tag+'-dependency-postcheck.json'))['unchanged'].values())
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(E/'dependencies'/package/rel)==d
 h=[x for x in load(E/'metadata'/tag/'harness-metadata.json')['proof_harnesses'] if x['pretty_name']==row['harness']];assert len(h)==1;h=h[0]
 assert not h['attributes']['verified_stubs']
 expected=[] if 'dealloc-check' in tag else [{'original':'std :: alloc :: dealloc','replacement':'frozen_release_dealloc'}]
 assert h['attributes']['stubs']==expected
 producer='prepare-sdk-release-'+('dealloc.py' if 'dealloc-check' in tag else 'owner-empty.py' if 'owner-empty' in tag else 'owner-drop.py')
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'source';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021'/producer),str(out)],check=True,stdout=subprocess.DEVNULL)
  for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),(tag,rel)
print(json.dumps(dict(accepted=len(q['accepted']),excluded=len(q['excluded']),scope=q['scope'],remaining=q['remaining']),indent=2))
