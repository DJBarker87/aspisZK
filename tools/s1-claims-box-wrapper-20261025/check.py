#!/usr/bin/env python3
"""Read-only native Box/IR packet check; rejects promotion to initialization."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-claims-box-wrapper-20261025';T=R/'tools/s1-claims-box-wrapper-20261025';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();m=json.loads((P/'manifest.json').read_text())
assert m['whole_initialization_proved'] is False and m['enclosing_premise_removed'] is False
for rel,h in m['files'].items():
 p=R/rel;assert sha(p)==h,rel
 assert p.suffix not in ['.out','.goto','.symtab','.llbc','.o','.olean','.rmeta','.rlib','.so','.dylib'],rel
source=(T/'proofs.rs').read_text();assert 'kani::assume' not in source and '#[kani::stub(' not in source and 'transmute' not in source
assert 'let base=out.as_mut_ptr();assert!(base.cast::<u8>()==raw)' in source
assert 'for p in 0..3 {out.as_mut_ptr().cast::<[QM31;29]>().add(p).write(rows[p]);}' in source
assert 'let initialized=out.assume_init()' in source and 'assert!(owner==raw)' in source
for n in range(1,5):
 d=E/f's1-claims-box-wrapper-v{n}';i=json.loads((d/'input.json').read_text());j=json.loads((d/'receipt.json').read_text());cmd=j['command']
 assert j['verification_launched']==(n%2==0) and j['watchdog_stop'] is None and j['swaps']==0
 assert all(j['source_unchanged'].values()) and all(j['tools_unchanged'].values())
 assert ('uninit-checks' in cmd)==(n>=3)
 assert j['exit_status']==(1 if n==4 else 0)
 assert '--unwinding-assertions' in cmd and i['environment']['RUSTFLAGS']=='-C opt-level=3 -Z mir-opt-level=0 -C overflow-checks=yes'
 for file,key in [('input.json','input_sha256'),('stdout.log','stdout_sha256'),('time.log','stderr_time_sha256')]:assert sha(d/file)==j[key]
 for f in (d/'source').rglob('*'):
  if f.is_file()and f.name!='run.py':assert sha(f)==i['source_files'][str(f.relative_to(d/'source'))]
 assert (d/'source/min/src/probe_claims_box_wrapper.rs').read_bytes()==(T/'probe.rs').read_bytes()
 assert source.startswith((d/'source/min/src/claims_box_wrapper.rs').read_text())
 for row in i['source_binding']['native_source_files']:
  assert i['source_files'][row['path']]==row['sha256']
  if row['source']=='crates/aspis-core/src/field.rs':
   frozen=subprocess.check_output(['git','show',row['revision']+':'+row['source']],cwd=R);assert hashlib.sha256(frozen).hexdigest()==row['sha256']
log=(E/'s1-claims-box-wrapper-v2/stdout.log').read_text();assert '0 of 153 failed' in log and '2 of 2 cover properties satisfied' in log
log=(E/'s1-claims-box-wrapper-v4/stdout.log').read_text();assert '1 of 142 failed' in log and '0 of 4 cover properties satisfied' in log and 'Interaction between raw pointers and unions is not yet supported.' in log and 'drop_in_place' in log
# v2 inspected symbols only; no body/read-footprint credit. Its old controller
# is a hash-exact reconstruction, explicitly not a contemporaneous snapshot.
d=E/'s1-claims-box-wrapper-ir-v2';i=json.loads((d/'input.json').read_text());assert sha(d/'controller-reconstruction.py')in i['pins'].values();assert len((d/'functions.txt').read_text().splitlines())==1
# v3 is the exact linked native IR selected by the actual wrapper proof.
d=E/'s1-claims-box-wrapper-ir-v3';j=json.loads((d/'receipt.json').read_text());assert j['exit_status']==0 and j['source_and_tool_unchanged']and j['watchdog_stop']is None
inv=json.loads((E/'s1-claims-box-wrapper-ir-audit-v1/inventory.json').read_text());assert inv['text_sha256']==sha(d/'functions.txt')and len(inv['selected_functions'])==22 and not inv['missing_calls']
for f in inv['selected_functions']:assert hashlib.sha256(f['body'].encode()).hexdigest()==f['body_sha256']
assert inv['normalized_as_mut_ptr'][2:5]==['ASSIGN V1 := address_of(*V2)','ASSIGN V0 := cast(V1, struct tag-_262990846129430720794961562193052722729[29][3]*)','SET RETURN VALUE V0']
assert all('alloc::alloc::alloc'not in f['name']and 'alloc::alloc::dealloc'not in f['name']and 'alloc::alloc::realloc'not in f['name']for f in inv['selected_functions'])
print(f'PASS {len(m["files"])} pins: DEFAULT native Box pointer/value coupling, exact cast-shape/22-helper inventory; UNINIT partial-drop failure retained. Whole initialization/source/SDK/S1/S6 remain OPEN.')
