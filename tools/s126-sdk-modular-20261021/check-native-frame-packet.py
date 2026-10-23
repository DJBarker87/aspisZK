#!/usr/bin/env python3
"""Audit source-only native prefix partitions. Does not replay solvers."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2]
O=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-native-frame-windows'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
manifest=read(O/'manifest.json')
assert manifest['schema']=='focused-extractor-proof-packet-v1'
assert {str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}==set(manifest['files'])
for rel,digest in manifest['files'].items():
 p=O/rel;assert p.suffix in ['.json','.log','.lean','.py','.rs','.toml','.lock'] or p.name=='lean-toolchain',p
 assert sha(p)==digest,rel
q=read(O/'qualification.json');accepted=q['accepted_frame'];assert len(accepted)==17
native=None;normalized=None;results=[]
for tag in accepted:
 receipt=read(O/'receipts'/tag/'receipt.json')
 assert receipt['exit_status']==10 and receipt['swaps']==0
 assert receipt['limits']['memory.max']=='8589934592' and receipt['limits']['memory.swap.max']=='0'
 inp=read(O/(tag+'-input.json'))
 assert '--property' not in inp['commands'][-1]
 assert not any('sdk_live_models' in str(x) for x in inp['harness_metadata']['attributes']['stubs'])
 source=[p for p in (O/'sources').glob('*/src/lib.rs') if sha(p)==inp['source_sha256']]
 assert len(source)==1,(tag,source)
 s=source[0].read_text();cut=read(source[0].parents[1]/'source-cut.json')
 assert cut['source_sha256']==sha(source[0])
 # Generator appends one separating newline after the pinned native prefix.
 body=s[:s.index('#[cfg(kani)] mod proofs')][:-1]
 assert hashlib.sha256(body.encode()).hexdigest()==cut['native_source_prefix_sha256']
 if native is None:native=body
 assert body==native
 assert 'aspis_s126_owned_sdk_borrowed' not in s
 assert 'let data_slots:[usize;3]=kani::any();' in s
 assert 'let initial_counts:[isize;3]=kani::any();' in s
 if 'window' in tag:
  i=int(re.search(r'window(\d+)',tag)[1]);root=0;audit=tag+'-audit'
  assert (cut['observer_root'],cut['observer_window'],cut['window_start'],cut['window_width'])==(0,i,4096*i,4096)
  needle=f'let offset:u16=kani::any();let selected_index:usize={4096*i}+(offset%4096) as usize;'
  assert s.count(needle)==1
  s=s.replace(needle,'let selected_index:usize=kani::any();')
 else:
  root=int(re.search(r'root(\d)',tag)[1]);audit=f'sdk-native-root{root}-audit-v1'
  assert cut['observer_root']==root
 s=s.replace(f'let selected_root:usize={root};','let selected_root:usize=ROOT;')
 if normalized is None:normalized=s
 assert s==normalized,(tag,'partition modified more than its ghost root/index')
 a=O/'receipts'/audit;data=read(a/'property-audit-v2.json')
 assert data['root']==root and data['proof_receipt_sha256']==sha(O/'receipts'/tag/'receipt.json')
 assert data['inventory_sha256']==sha(a/'stdout.log')
 assert data['property_report_sha256']==sha(a/'properties-complete-v2.json')
 assert data['raw_log_sha256']==sha(O/'diagnostics'/tag/'step7.log')
 inv=[p for item in read(a/'stdout.log') for p in item.get('properties',[])]
 report=read(a/'properties-complete-v2.json')
 ids={p['name'] for p in inv};assert len(ids)==len(inv)
 assert ids=={p['property'] for p in report} and len(report)==len(inv)
 covers={p['name'] for p in inv if p['class']=='cover'};assert len(covers)==2
 assert all(p['status']==('FAILURE' if p['property'] in covers else 'SUCCESS') for p in report)
 assert data['inventory_properties']==len(inv) and data['noncover_successes']==len(inv)-2
 results.append(dict(target=tag,noncover_successes=len(inv)-2,wall_seconds=receipt['wall_seconds'],peak_rss_kib=receipt['peak_rss_kib'],swaps=receipt['swaps']))
lean=O/'receipts/sdk-native-frame-coverage-v2';audit=read(lean/'lean-audit.json')
assert audit['exit_status']==0 and audit['swaps']==0
assert audit['source_sha256']==sha(lean/'source.lean')==sha(O/'lean/S2SdkNativeFrameCoverageV1.lean')
current=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/S2SdkNativeFrameCoverageV1.lean'
assert sha(current)==audit['source_sha256']
assert len(audit['print_axioms'])==4
assert all(re.search(r'depends on axioms:\s*\[propext, Quot.sound\]',s) for s in audit['print_axioms'])
assert '-j1' in audit['command'] and '-M4400' in audit['command']
facts='sdk-native-entry-facts-v1';inp=read(O/(facts+'-input.json'))
assert '--property' not in inp['commands'][-1]
props=[p for item in read(O/'diagnostics'/facts/'property-inventory.json') for p in item.get('properties',[])]
rows=read(O/'diagnostics'/facts/'properties-without-traces.json')
assert len(props)==len(rows)==len({p['property'] for p in rows})
assert {p['name'] for p in props}=={p['property'] for p in rows}
covers={p['name'] for p in props if p['class']=='cover'};assert len(covers)==2
assert all(p['status']==('FAILURE' if p['property'] in covers else 'SUCCESS') for p in rows)
assert read(O/'receipts'/facts/'receipt.json')['exit_status']==10
assert inp['source_sha256']==sha(O/'sources/sdk-shared-prefix-entry-facts-v1/src/lib.rs')
print(json.dumps(dict(schema='focused-extractor-proof-packet-v1',checked_partitions=results,entry_facts_noncover_successes=len(props)-2,lean_audit=audit['print_axioms'],qualification=q['qualification']),indent=2))
