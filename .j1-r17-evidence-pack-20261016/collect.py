#!/usr/bin/env python3
"""Collect existing serial build evidence; never execute a compiler."""
from pathlib import Path
import hashlib,json,tarfile
W=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted')
O=W/'evidence-primary-432-20261016';O.mkdir(exist_ok=False)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def read(p):return json.loads(p.read_text())
def write(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
manifest=read(W/'sources/SOURCE-MANIFEST.json')
for n,m in manifest['modules'].items():assert sha(W/'sources'/m['stage_as'])==m['source_sha256'],n
runs=['fields-432-a','whole-432-a','carrier-432-a','public-bridge-432-a','parser-432-a','public-bridge-432-b','current-qm-432-a']
rows=[];compiled=[]
for run in runs:
 d=W/'runs'/run;c=read(d/'complete.json');assert c['exit_status']==0
 r=[]
 for p in sorted(d.glob('*/receipt.json')):
  x=read(p);assert x['exit_status']==0 and x['axioms']['passed'];assert x['cgroup_swap_current']=='0' and x['process_swaps']==0
  x['run']=run;compiled.append(x)
  r.append({k:x[k] for k in ['target','exit_status','wall_seconds','sampled_cgroup_peak_bytes','peak_process_rss_kib','process_swaps']})
 rows.append({'run':run,'targets':c['targets'],'reused':c['reused'],'newly_checked':r})
final=[]
for p in sorted((W/'successful-targets').glob('*.json')):
 x=read(p);n=x['target'];assert x['key']['source_sha256']==manifest['modules'][n]['source_sha256'],n
 for obj in x['objects'].values():assert sha(Path(obj['path']))==obj['sha256']
 final.append(x)
assert len(final)==69,len(final)
assert len(compiled)==70,len(compiled)
assert not any('SelectedMask' in x['target'] or x['target'].startswith('ExtractedMask') for x in final)
summary={'scope':'Focused Lean 4.32 extracted public/parser chains plus unchanged current-QM31 equality dependency closure. No Rust execution/extraction or runtime-cost claim. No selected-mask replay.',
 'source_base':manifest['source_base'],'final_owned_source_commit':'c2f8dc7f9b0699a52710b8f9777987ded1773173','source_manifest_sha256':sha(W/'sources/SOURCE-MANIFEST.json'),
 'snapshot_sha256':sha(W/'external-inputs-002.json'),'external_module_count':len(read(W/'external-inputs-002.json')['modules']),
 'backend_evidence_commit':'8b5661efb','unique_compiled_modules':len(final),'successful_compile_attempts':len(compiled),'failed_lean_attempts':0,
 'tooling_failure':'snapshot-a failed before any Lean invocation on an embedded JavaScript import; original metadata and repaired header-scanner regression retained',
 'source_changes':'Only the new composition documentation header changed between its two successful checks; all theorem bodies and all other 84 inventoried Lean files unchanged.',
 'no_old_objects':'Empty project object root; all 69 outputs newly compiled with the pinned 4.32 runtime. External closure rejects 4.31 olean headers and verifies runtime/source/import/companion pins.',
 'limits':{'MemoryHigh':6*2**30,'MemoryMax':8*2**30,'MemorySwapMax':0,'lean_options':['-j1','-M0']},
 'max_process_rss_kib':max(x['peak_process_rss_kib'] for x in compiled),'max_sampled_cgroup_bytes':max(x['sampled_cgroup_peak_bytes'] for x in compiled),
 'all_process_swaps_zero':True,'all_cgroup_swap_current_zero':True,'total_compile_wall_seconds':round(sum(x['wall_seconds'] for x in compiled),3),
 'requested_axiom_reports_final':sum(x['axioms']['requested_count'] for x in final),
 'allowed_axioms':['propext','Classical.choice','Quot.sound'],'zero_requested_audits_make_no_axiom_claim':True,
 'final_public_source_sha256':manifest['modules']['ExtractedPublicCheckedBridge432']['source_sha256'],
 'final_public_objects':next(x['objects'] for x in final if x['target']=='ExtractedPublicCheckedBridge432'),
 'runs':rows,'compile_only_unchecked_inventory':[n for n in manifest['topological_order'] if n not in {x['target'] for x in final}],
 'remaining_boundaries':['Rust/extractor correctness','actual verifier caller reachability of the payment helper','omitted metadata/account binding and independently supplied public equality','parser M31 descent','selected-mask whole-loop and sampler composition','J1.R16 syscall semantics'],
 'retained_host_objects':str(W/'objects'),'bundle_exclusions':'Compiled objects/IR are retained on host; duplicate per-run external-inputs.json copies are replaced by the identical shared external-inputs-002.json. Source/object hashes remain in receipts.'}
write(O/'SUMMARY.json',summary)
files={}
def add(p,name=None):
 assert p.is_file() and not p.is_symlink(),p
 files[name or str(p.relative_to(W))]=p
for p in (W/'sources').rglob('*'):
 if p.is_file():add(p)
for p in (W/'source-revisions').rglob('*'):
 if p.is_file():add(p)
for run in runs:
 for p in (W/'runs'/run).rglob('*'):
  if p.is_file() and 'artifacts' not in p.parts and p.name!='external-inputs.json':add(p)
 add(W/(run+'.console.log'))
for p in (W/'successful-targets').glob('*.json'):add(p)
for n in ['external-inputs-002.json','snapshot-a-failure.json','snapshot-b.log','j1-r17-build-extracted.py','j1-r17-build-extracted-v2.py','staging-pins.json']:
 add(W/n)
for n in ['backend-final-manifest.json','aeneas-lean432.patch','dependency-cache-pins.json']:
 add(W.parent/n,'external-provenance/'+n)
add(O/'SUMMARY.json','SUMMARY.json')
add(Path(__file__),'collect.py')
write(O/'BUNDLE-MANIFEST.json',{n:{'sha256':sha(p),'bytes':p.stat().st_size} for n,p in sorted(files.items())})
files['BUNDLE-MANIFEST.json']=O/'BUNDLE-MANIFEST.json'
with tarfile.open(O/'evidence.tar.gz','w:gz') as t:
 for n,p in sorted(files.items()):t.add(p,arcname=n,recursive=False)
write(O/'archive-pin.json',{'archive':'evidence.tar.gz','sha256':sha(O/'evidence.tar.gz'),'bytes':(O/'evidence.tar.gz').stat().st_size,'member_count':len(files)})
print(json.dumps({k:summary[k] for k in ['unique_compiled_modules','successful_compile_attempts','max_process_rss_kib','max_sampled_cgroup_bytes','total_compile_wall_seconds','requested_axiom_reports_final']},indent=2))
print((O/'archive-pin.json').read_text())
