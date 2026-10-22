#!/usr/bin/env python3
"""Check audited source-only native constructor evidence, without proof replay."""
from pathlib import Path
import json,hashlib,tempfile,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-first-pair'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc'] for p in E.rglob('*'))
a=load(E/'case/pair-audit.json');q=load(E/'qualification.json');tag=q['tag'];i=load(E/(tag+'-input.json'));r=load(E/'receipts'/tag/'receipt.json')
assert r['exit_status']==10 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
assert a['noncover_successes']==5482 and len(a['reached_covers'])==2
props=load(E/'case/properties-complete.json');assert len(props)==5484 and len({x['property'] for x in props})==5484
assert all(x['status']==('FAILURE' if x['property'] in a['reached_covers'] else 'SUCCESS') for x in props)
assert sha(E/'source/src/lib.rs')==i['source_sha256']==q['source_sha256']
h=i['harness_metadata'];assert h['attributes']['kind']=='Proof' and not h['attributes']['verified_stubs']
assert not any('AccountInfo' in str(x) or 'sdk_live_models' in str(x) for x in h['attributes']['stubs'])
cg=load(E/'sdk-shared-prefix-codegen-first-image-pair-v1-input.json');assert '-C opt-level=3' in cg['env']['RUSTFLAGS']
for package,pin in cg['local_dependency_source_pins'].items():
 for rel,d in pin['files'].items():assert sha(E/'dependencies'/package/rel)==d
assert all(load(E/'sdk-shared-prefix-codegen-first-image-pair-v1-dependency-postcheck.json')['unchanged'].values())
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'source';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-image-pair.py'),str(out)],check=True,stdout=subprocess.DEVNULL)
 for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(E/'source'/rel).read_bytes(),rel
print(json.dumps(dict(checks=5482,covers=2,scope=q['scope'],remaining=q['remaining']),indent=2))
