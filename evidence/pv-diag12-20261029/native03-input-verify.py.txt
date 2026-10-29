from pathlib import Path
import json,hashlib,re,sys,subprocess,datetime
D=Path('/home/dombarker/project-offloads/codex-pv-diag12-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
phase=sys.argv[1]
freeze=json.loads((D/'freeze-sources.json').read_text())
ext=json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert sha(Path(r['path']))==r['object_sha256']
reuse=json.loads((D/'reuse.json').read_text())['rows']
for r in reuse:
 assert sha(Path(r['path']))==r['sha256'] and sha(Path(r['source']))==r['source_sha256']
for r in json.loads((D/'rust-src-pins.json').read_text()):
 assert sha(Path(r['path']))==r['sha256']==sha(D/r['snapshot'])
for r in json.loads((D/'serde-json-pins.json').read_text())['sources']:
 assert sha(Path(r['path']))==r['sha256']==sha(D/r['snapshot'])
receipts=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))]
assert len({r['attempt'] for r in receipts})==len(receipts)
assert all(67300<=r['attempt']<=67399 for r in receipts)
for r in receipts:
 assert r['admission_exit']==0 and r['admission_allowed'] is True and r['swaps']=='0'
 assert sha(D/('lean'+str(r['attempt'])+'-source.lean.txt'))==r['source_sha256']
 if r['exit']==0:
  assert 'sorryAx' not in r['print_axioms']
  for ax in re.findall(r'depends on axioms: \[([^]]*)\]',r['print_axioms']):
   assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'}
# Never resubmit unchanged failed source. This also checks earlier successful
# sources recompiled under new dependencies were not identical to a failure.
failed=set()
for r in receipts:
 assert r['source_sha256'] not in failed,('unchanged failed source',r['attempt'])
 if r['exit']!=0:failed.add(r['source_sha256'])
final=[]
for m,pin in freeze['sources'].items():
 p=D/'sources'/(m+'.lean');assert sha(p)==pin['sha256']
 hits=[r for r in receipts if r['module']==m and r['exit']==0 and r['source_sha256']==pin['sha256']]
 if not hits:
  assert phase=='preaudit' and m in ['PV_DIAG12_Audit','PV_DIAG12_ProducerAudit','PV_DIAG12_FinalManifest'];continue
 r=hits[-1];assert sha(D/'objects'/(m+'.olean'))==r['object_sha256']
 for files in r['dependency_objects'].values():
  for f,h in files.items():assert sha(Path(f))==h,(m,f)
 final.append(dict(module=m,attempt=r['attempt'],source_sha256=pin['sha256'],object_sha256=r['object_sha256']))
# Verify frozen feature-resolution evidence without rerunning unchanged Cargo.
P=D.parent/'codex-pv-diag11-20261029'
features=json.loads((P/'resolved-features.json').read_text());assert features['exit']==0
lock=D.parent/'codex-pv-fscan-20261028/src/tools/r1-cost-probe/Cargo.lock'
assert sha(lock)==features['lock_sha256']
(D/'resolved-features-reused.json').write_bytes((P/'resolved-features.json').read_bytes())
# Record exact unresolved callbacks for the requested first channel.
residual=dict(json=dict(source='serde_json 1.0.151 value/mod.rs:223-259',open=['Value::Serialize recursive variant/number/string/map/sequence bodies and token order','WriterFormatter UTF-8 conversion / Formatter::write_str dispatch','io_error(fmt::Error) allocates io::Error::new(Other, "fmt error") before mapping back to fmt::Error','default_write_fmt adapter error slot/store, native callbacks and all cleanup/unwind','association of chunk pointers/capacity/allocator requests, not only concatenated bytes']),stdout=dict(source='std 1.94.1 io/stdio.rs',open=['OUTPUT_CAPTURE_USED and OUTPUT_CAPTURE TLS/mutex branches and restore/drop','STDOUT OnceLock init/allocation: actual LineWriter buffer capacity/pointers','ReentrantLock current_id/owner/count, overflow expect, mutex spin/futex path and guard unlock','RefCell borrow guard and borrow-panic path; callback reentrancy','cleanup try_lock and LineWriter replacement/drop, including pending buffered output','print_to panic/hook/error Display and error destruction on returned I/O error']),boundary=dict(open=['libc write/open64/close expansion to kernel syscall requests, cancellation/TLS/errno state','fd-drop UB-check specialization; enabled path includes fcntl and abort output','CStr/NUL path conversion and validation error allocation/drop','native pointer/count contract, live BufGuard/Vec drain/copy and unwind states','observer event/terminal and readout association for every abnormal prefix']),compiler='V370 / D381 / D386 retained',optionB='P: failure event witness-independent. Signal is arbitrary in these definitions; it is not proved public.',complete_deployed_JSON_Step=False,complete_deployed_JSON_Readout=False)
(D/'residual-inventory.json').write_text(json.dumps(residual,indent=2)+'\n')
# Generator final-source equality checked from the transported frozen plan.
plans=json.loads((D/'plans.json').read_text());generated={p['module']:p for p in plans}
for m,p in generated.items():assert sha(D/'sources'/(m+'.lean'))==p['sha256']
report=dict(phase=phase,external_objects=len(ext),reused_project_objects=len(reuse),source_revision=freeze['revision'],sources=final,attempts=len(receipts),accepted=sum(r['exit']==0 for r in receipts),rejected=[r['attempt'] for r in receipts if r['exit']!=0],mismatches=[],generator_final_sources=len(generated),resolved_feature_crates=len(features['crates']),scope='focused DIAG12 source-layer replay; no frozen privacy-release manifest')
(D/('verification-'+phase+'.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='sources'}))
