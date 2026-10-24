#!/usr/bin/env python3
"""Source-only, read-only validation of finish bindings and native selectors."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'s1-finish-selectors-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((P/'source-pins.json').read_text())
for path,rows in pins['unchanged_complete_files'].items():
 assert len(set(rows.values()))==1
 for rev,h in rows.items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',rev+':'+path])).hexdigest()==h
for path,h in pins['reused_sources'].items():assert sha(R/path)==h
source=(R/'tools/s1-finish-selectors-20261024/lib.rs').read_text()
assert all(source.count(e)==1 for e in pins['native_expressions'])
proof=(R/'tools/s1-finish-selectors-20261024/proofs.rs').read_text()
assert 'kani::stub' not in proof and 'kani::assume' not in proof
assert '[[[u32; 4]; 29]; 3]' in proof and 'Box::new(input)' in proof
model=B/'lean-candidates/s126-caller-boundary-20261021/S1FinishMaskSourceV1.lean'
old=(B/'evidence/terminal-v4-external-model-integration-20261019/root-current-shared-mask-remainder-v3-20261019/source.lean').read_text();old=old[old.index('/-- [aspis_r1_mask_extraction_probe'):old.index('end AspisR1SelectedMaskProbe')].strip()
copy=re.sub(r'^def ([A-Za-z0-9_.]+)',r'def sourceCopy.\1',old,flags=re.M)
new=model.read_text();new=new[new.index('/-- [aspis_r1_mask_extraction_probe'):new.index('theorem source_body_0')].strip();assert new==copy
m=json.loads((P/'targets.json').read_text())
for name,attempt in m['targets'].items():
 d=E/attempt;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['target']==name
 assert sha(d/'source.lean')==r['source_sha256']==sha(B/'lean-candidates/s126-caller-boundary-20261021'/(name+'.lean'))
 assert r['print_axioms']
 for text in r['print_axioms']:
  matches=re.findall(r'\[(.*?)\]',text,re.S)
  if matches:assert set(matches[0].replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|axiom|native_decide|bv_decide)\b|set_option (maxHeartbeats|maxRecDepth)',(d/'source.lean').read_text())
 if name=='S1FinishMaskSourceV1':assert len(r['print_axioms'])==25
imp=json.loads((E/'s1-finish-children-import-pins.json').read_text())
for name,attempt in m['targets'].items():assert imp['targets'][name]['source_sha256']==json.loads((E/attempt/'receipt.json').read_text())['source_sha256']
ns=json.loads((P/'namespace-cache-selected.json').read_text())
actual={r['path']:r['sha256'] for r in imp['modules']}
for rel,row in ns['selected'].items():
 if rel.endswith('.olean'):assert actual[ns['overlay']+rel]==row['sha256']
 if 'companion_of' in row:assert row['companion_of'] in ns['selected']

d=P/'host/results'/m['native_target'];r=json.loads((d/'receipt.json').read_text());inputs=json.loads((d/'input.json').read_text())
assert sha(d/'input.json')==r['input_sha256']
assert r['exit_status']==0 and r['swaps']==0 and r['cgroup_swap_current']==0 and r['native_imports_unchanged']
assert all(r['sources_unchanged'].values())
assert r['limits']['memory.max']==str(2*2**30) and r['limits']['memory.swap.max']=='0'
assert '--unwinding-assertions' in r['command'] and inputs['environment']['RUSTFLAGS'].startswith('-C opt-level=3 ')
log=(d/'stdout.log').read_text();assert '0 of 467 failed' in log and 'VERIFICATION:- SUCCESSFUL' in log and '1 successfully verified harnesses, 0 failures' in log
imports=inputs['native_imports'];assert any(x.endswith('/lib/libstd.rlib') for x in imports)
assert any('librustc_driver' in x for x in imports) and any('libcore-' in x for x in imports)
assert inputs['rustc_version']=='rustc 1.93.0-nightly (53732d5e0 2025-11-20)'
crate=next(v for p,v in inputs['source_pins'].items() if 's1-finish-selectors-v1' in p)
for file in ['lib.rs','proofs.rs']:assert crate['src/'+file]==sha(R/'tools/s1-finish-selectors-20261024'/file)
for file in ['admit-host.py','run-host.py']:assert crate[file]==sha(R/'tools/s1-finish-selectors-20261024'/file)
a=json.loads((P/'host'/(m['native_target']+'-admission.json')).read_text());assert a['admitted'] and a['root']=='/sys/fs/cgroup'
assert a['reserved_bytes']+a['additional_bytes']+a['uncapped_background_allowance_bytes']<a['limit_bytes']
for path,h in json.loads((P/'tool-pins.json').read_text())['files'].items():assert sha(R/path)==h
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.a','.o'] for p in P.rglob('*') if p.is_file())
print(json.dumps(dict(status='PASS',lean=m['metrics'],native_checks=467,native_wall_seconds=r['wall_seconds'],native_peak_rss_bytes=r['peak_rss_kib']*1024,native_import_files=len(imports),scope=m['qualification'])))
