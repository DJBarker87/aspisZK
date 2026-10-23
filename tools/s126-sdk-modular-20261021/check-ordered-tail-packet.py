#!/usr/bin/env python3
"""Check ordered-tail link and prerequisite frame packets without solver replay."""
from pathlib import Path
import json,hashlib,subprocess,tempfile
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-ordered-tail';T=R/'tools/s126-sdk-modular-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for rel,d in load(E/'manifest.json')['files'].items():assert sha(E/rel)==d,rel
assert not any(p.suffix in ['.out','.o','.olean','.rlib','.llbc'] for p in E.rglob('*'))
q=load(E/'qualification.json');rows=q['targets'];assert sum(x['accepted'] for x in rows.values())==4
expected={'sdk-modular-owner-step-check-v3':(507,3,4),'sdk-raw-drop-shared-check-v2':(780,3,3),'sdk-raw-drop-exclusive-check-v2':(760,3,3),'sdk-ordered-tail-links-raw-check-v2':(2627,5,5)}
for tag,x in rows.items():
 P=E/'sources'/x['source'];r=load(E/'receipts'/tag/'receipt.json');i=load(E/(tag+'-input.json'))
 assert sha(P/'src/lib.rs')==i['source_sha256']==x['source_sha256']
 assert r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3 and r['swaps']==0
 assert all(load(E/(tag+'-dependency-postcheck.json'))['unchanged'].values())
 for package,pin in i['local_dependency_source_pins'].items():
  for rel,d in pin['files'].items():assert sha(E.parent/'sdk-release-allocator/dependencies'/package/rel)==d
 if not x['accepted']:continue
 assert r['exit_status']==0 and '-C opt-level=3' in i['env']['RUSTFLAGS'] and '--unwinding-assertions' in i['command']
 checks,covers,total=expected[tag];assert (x['noncover_successes'],x['reached_covers'],x['all_cover_locations'])==(checks,covers,total)
 log=(E/'receipts'/tag/'stdout.log').read_text();assert f'0 of {checks} failed' in log and f'{covers} of {total} cover properties satisfied' in log
 h=next(h for h in load(E/'metadata'/tag/'harness-metadata.json')['proof_harnesses'] if h['pretty_name']==x['harness'])
 if 'owner-step' in tag:
  assert h['attributes']['kind']=={'ProofForContract':{'target_fn':'destroy_owner'}} and not h['attributes']['verified_stubs']
 elif 'raw-drop' in tag:
  kind='shared' if 'shared' in tag else 'exclusive'
  assert h['attributes']['kind']=={'ProofForContract':{'target_fn':'finish_guard_'+kind}} and not h['attributes']['stubs'] and not h['attributes']['verified_stubs']
 else:
  assert h['attributes']['kind']=='Proof'
  assert set(h['attributes']['verified_stubs'])=={'proofs::finish_guard_shared','proofs::finish_guard_exclusive','proofs::destroy_owner','encoded_finish'}
 if 'raw-drop' not in tag:assert h['attributes']['stubs']==[{'original':'std :: alloc :: dealloc','replacement':'frozen_release_dealloc'}]
for source,producer in [('sdk-modular-ordered-tail-v3','prepare-sdk-modular-ordered-tail.py'),('sdk-ordered-tail-links-raw-v2','prepare-sdk-ordered-tail-raw.py')]:
 with tempfile.TemporaryDirectory() as d:
  out=Path(d)/'source';subprocess.run(['python3',str(T/producer),str(out)],check=True,stdout=subprocess.DEVNULL)
  for rel in ['src/lib.rs','Cargo.toml']:assert (out/rel).read_bytes()==(E/'sources'/source/rel).read_bytes(),(source,rel)
# The exact existing copy contract/body remains the prerequisite, never a renamed different leaf.
owner=(E.parent/'sdk-parent-cuts/sources/sdk-finish-fixed-frame-v5/src/lib.rs').read_text();a=owner.index('fn native_finish(');b=owner.index('#[cfg(kani)] mod proofs',a)
assert owner[a:b] in (E/'sources/sdk-ordered-tail-links-raw-v2/src/lib.rs').read_text()
print(json.dumps(dict(accepted=4,excluded=5,scope=q['scope'],remaining=q['remaining']),indent=2))
