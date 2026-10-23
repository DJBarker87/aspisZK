#!/usr/bin/env python3
"""Check conditional successful reference constructor; never promote to native S2."""
from pathlib import Path
import json,hashlib,subprocess,tempfile,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';E=B/'sdk-reference-first'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,d in load(E/'manifest.json')['files'].items():assert sha(E/n)==d,n
assert not any(p.suffix in ['.out','.o','.rlib','.llbc'] for p in E.rglob('*'))
tag='sdk-reference-first-cut-v3';cg='sdk-shared-prefix-codegen-reference-first-v3';i=load(E/(tag+'-input.json'));c=load(E/(cg+'-input.json'));r=load(E/'receipts'/tag/'receipt.json')
assert r['exit_status']==10 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
assert i['source_scope']=='conditional_borrowed_reference_success' and i['source_sha256']==c['source_sha256']==sha(E/'source/src/lib.rs')
assert load(E/(cg+'-dependency-postcheck.json'))['unchanged']=={n:True for n in c['local_dependency_source_pins']}
for name,pin in c['local_dependency_source_pins'].items():
 for rel,d in pin['files'].items():assert sha(E/'dependencies'/name/rel)==d
assert (E/'dependencies/aspis-s126-owned-sdk-borrowed/src/lib.rs').read_bytes()==(B/'sdk-parent-cuts/sources/owned-sdk-borrowed-v1/src/lib.rs').read_bytes()
row=i['harness_metadata'];assert row['attributes']['kind']=='Proof' and len(row['attributes']['stubs'])==5 and not row['attributes']['verified_stubs']
assert not any('AccountInfo::' in str(x) or 'sdk_live_models' in str(x) for x in row['attributes']['stubs'])
assert '--property' not in i['commands'][-1] and '--unwinding-assertions' in i['commands'][-1]
props=[p for x in load(E/'case/property-inventory.json') for p in x.get('properties',[])];expected={p['name']:p for p in props};assert len(props)==len(expected)==4197
rows=[];current=None;block=[]
for line in (E/'case/all-properties.log').read_text().splitlines():
 end=line.find('] ') if line.startswith('[') else -1
 while end>=0 and line[1:end] not in expected:end=line.find('] ',end+2)
 if end>=0:assert current is None;current=line[1:end];block=[line[end+2:]]
 elif current is not None:block.append(line)
 if current is not None:
  m=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
  if m:rows.append(dict(property=current,description=m[1],status=m[2]));current=None;block=[]
assert current is None and rows==load(E/'case/properties-complete.json')
actual={p['property']:p for p in rows};assert len(actual)==len(rows) and actual.keys()==expected.keys()
covers=[p['name'] for p in props if p['class']=='cover'];assert len(covers)==2
assert all(p['status']==('FAILURE' if p['property'] in covers else 'SUCCESS') for p in rows)
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'reference';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-reference-first-cut.py'),str(out)],check=True)
 for rel in ['src/lib.rs','Cargo.toml','source-cut.json']:assert (out/rel).read_bytes()==(E/'source'/rel).read_bytes(),rel
print(json.dumps(dict(target=tag,noncover_successes=4195,reached_covers=2,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axioms='N/A bounded Kani, no new Lean theorem',qualification='Conditional complete borrowed-reference success and same decoded first/None/fixed-input/checkpoint-output facts. Native SDK/source child/gate/scan/runtime/oracle composition remains.'),indent=2))
