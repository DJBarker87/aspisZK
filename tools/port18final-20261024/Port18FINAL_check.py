#!/usr/bin/env python3
"""Final source/object/receipt audit. No Lean invocation, historical writes, or native claim."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, sys
R=Path(__file__).resolve().parents[2]
E=R/'evidence/port18final-20261024'; V=R/'evidence/port18validate-20261024'
H=R/'evidence/port18coherence-20261024'; L=R/'docs/research/100bit-spend-path-20261013/lean'
T=R/'tools/port18final-20261024'; O=Path('/tmp/port18coherence-local-objects')
BASE='01f9c7adf8e1994df051b2aea7009601bc34bcaf'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def record(p):
 p=Path(p);return {'path':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def load(p):return json.loads(Path(p).read_text())
def revision():return subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
def standard(lines):
 assert len(lines)==17
 for line in lines:
  m=re.search(r'\[([^]]*)\]',line)
  assert m and set(m[1].replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'},line

def inspect():
 assert subprocess.check_output(['git','branch','--show-current'],cwd=R,text=True).strip()=='codex/cx-port17release-20261024'
 changed=subprocess.check_output(['git','diff','--name-only',BASE],cwd=R,text=True).splitlines()
 untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
 assert all(p.startswith(('tools/port18final-20261024/','evidence/port18final-20261024/')) for p in changed+untracked),(changed,untracked)
 old=[]
 for directory in [V,H,R/'tools/port18validate-20261024',R/'tools/port18coherence-20261024']:
  old.extend(record(p) for p in sorted(directory.rglob('*')) if p.is_file())
 receipts=[load(p) for p in sorted(V.glob('lean-*/receipt.json'))]
 assert len(receipts)==8
 accepted={r['target']:r for r in receipts if r['accepted']}
 assert len(accepted)==6
 for r in receipts:
  for f,h in r['source_hashes'].items():assert sha(V/r['attempt']/'sources'/f)==h
 compat=load(H/'lean-014/receipt.json')
 stages={**accepted,'Port18COHERENCE_CompatibilityLoad':compat}
 objects={};sources={}
 for target,r in stages.items():
  assert r['exit_status']==0 and r['swaps']==0
  for f,h in r['source_hashes'].items():
   assert sha(L/f)==h,(target,f)
   sources[f]=record(L/f)
  for n,d in r['deps_fingerprint']['objects'].items():assert sha(d['path'])==d['sha256'],(target,n)
  obj=O/(target+'.olean');assert sha(obj)==r['object_sha256'],target
  # Include every extant logical module part, not just the direct .olean.
  objects[target]=[record(p) for p in [obj,Path(str(obj)+'.server'),Path(str(obj)+'.private')] if p.is_file()]
 old_kernel=subprocess.check_output(['git','show','1e2b6fe7e9439687bb60ea4a26e3b6b3c094d46b:docs/research/100bit-spend-path-20261013/lean/Port18COHERENCE_Kernel.lean'],cwd=R)
 assert (L/'Port18COHERENCE_Kernel.lean').read_bytes().split(b'import Lean',1)[1]==old_kernel.split(b'import Lean',1)[1]
 audit=load(H/'lean-028/receipt.json');standard(audit['print_axioms'])
 for f,h in audit['source_hashes'].items():assert sha(L/f)==h;sources[f]=record(L/f)
 probe=(V/'lean-004/stdout.log').read_text()
 assert probe.count('REJECTED ')==7 and 'ACCEPTED exact valid : True := True.intro and dependent consumer' in probe
 assert 'disposable environments only' in probe
 canonical=load(H/'canonical-manifest.json')
 assert canonical['matching_selected_declarations']==15241 and canonical['fresh_project_declarations']==10375
 root_sources={};historical_sources={}
 for module in canonical['modules']:
  s=module['source']
  if 'path' not in s:continue
  if module['side']=='root':
   assert sha(R/s['path'])==s['sha256'],s['path']
   root_sources[s['path']]=record(R/s['path'])
  else:
   # Read immutable Git blobs only; never access session A worktrees.
   key=(s['revision'],s['path'])
   if key not in historical_sources:
    blob=subprocess.check_output(['git','show',s['revision']+':'+s['path']],cwd=R)
    assert hashlib.sha256(blob).hexdigest()==s['sha256'],key
    historical_sources[key]={'revision':s['revision'],'path':s['path'],'sha256':s['sha256'],'bytes':len(blob)}
 snap=Path('/tmp/port18coherence-snapshot-manifest.json');s=load(snap)
 assert sha('/tmp/port18coherence-snapshots.tsv')==s['tsv_sha256']
 assert s==load(H/'transport-manifest.json')
 for entry in s['snapshots']:assert sha(entry['path'])==entry['sha256'] and Path(entry['path']).stat().st_size==entry['bytes']
 for p in E.rglob('*'):
  if p.is_file():assert p.stat().st_size<=5000000,p
 return {'historical_files':old,'checked_objects':objects,'maintained_audit_sources':sources,
         'maintained_root_sources':root_sources,'immutable_candidate_source_blobs':list(historical_sources.values()),
         'snapshot_manifest':record(snap),'snapshot_tsv':record('/tmp/port18coherence-snapshots.tsv'),
         'canonical_manifest':record(H/'canonical-manifest.json'),
         'toolchain':record('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),
         'lake':record('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake'),
         'launcher':record(T/'Port18FINAL_local.py'),'checker':record(Path(__file__))}

mode=sys.argv[1] if len(sys.argv)>1 else '--check'
current=inspect()
if mode=='--preflight':
 out={'schema':'port18-final-source-dependency-preflight-v1','source_revision':revision(),
      'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**current,
      'historical_audit_assessment':'audit028 remains historical; refreshed stage objects may be byte-identical. New result is a separate final-source import check, not a new identity gate.',
      'source_assessment':'Maintained root source bytes checked; immutable candidate source blobs checked via Git; prior source/object associations reused. External full module sources/IR/native/release identity not newly certified.'}
 with (E/'preflight.json').open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
 print('PASS source/object preflight; no charged Lean attempt')
else:
 pre=load(E/'preflight.json')
 for k,v in current.items():assert pre[k]==v,k
 if mode=='--guard':
  print('PASS fresh source/object guard under shared atomic local Lean lock')
 else:
  assert mode=='--check'
  receipts=[load(p) for p in sorted(E.glob('lean-*/receipt.json'))]
  reservations=list(T.glob('lean-*.json'));assert 1<=len(reservations)<=2 and len(receipts)==len(reservations)
  a=receipts[-1];assert a['target']=='Port18COHERENCE_CheckedAudit' and a['accepted'] and a['exit_status']==0 and a['swaps']==0 and a['stopped'] is None
  assert a['final_preflight_sha256']==sha(E/'preflight.json') and a['final_dependency_closure']==current['checked_objects']
  assert a['tool_sha256']==current['toolchain']['sha256'] and a['launcher_sha256']==current['launcher']['sha256'] and a['checker_sha256']==current['checker']['sha256']
  assert a['env']['LEAN_PATH']==str(O)+':/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'
  for f,h in a['source_hashes'].items():assert sha(L/f)==h and sha(E/a['attempt']/'sources'/f)==h
  for n,d in a['deps_fingerprint']['objects'].items():assert sha(d['path'])==d['sha256']
  assert sha(O/(a['target']+'.olean'))==a['object_sha256']
  log=(E/a['attempt']/'stdout.log').read_text()
  assert log.count('\nIDENTICAL ')+int(log.startswith('IDENTICAL '))==15241
  assert 'Exact full declarations/types/proof and opaque values verified: 15241' in log
  assert not re.search(r'PANIC|error(?:\(|:)',log)
  standard(a['print_axioms'])
  historical=load(H/'lean-028/receipt.json')
  assert a['print_axioms']==historical['print_axioms']
  # pp.all reports and hidden structure/program boundary reports must survive in full.
  old_log=(H/'lean-028/stdout.log').read_text()
  suffix=old_log[old_log.index(historical['print_axioms'][0]):]
  assert log[log.index(a['print_axioms'][0]):]==suffix,'complete types/hidden structures or axioms changed'
  n=len(reservations);actual=len(receipts)
  out={'schema':'focused-extractor-proof-packet-v1','source_revision':revision(),'entry_charged':312,'entry_actual_lean':307,'entry_pre_lean':5,
       'new_charged':n,'new_actual_lean':actual,'new_pre_lean':n-actual,'continuation_allowance':2,'unused_continuation':2-n,
       'cumulative_charged':312+n,'cumulative_actual_lean':307+actual,'cumulative_pre_lean':5+n-actual,'ceiling':356,'remaining':44-n,
       'port20':'separate12/combined368 untouched','kani':'0/20 unchanged','new_kani_rust_backend_extraction':0,'full_frozen_manifest':False,
       'status':'PASS separately checked final-source logical closure; no native/release identity claim','receipt':a,
       'preflight':record(E/'preflight.json'),'stdout':record(E/a['attempt']/'stdout.log'),'time':record(E/a['attempt']/'time.log'),
       'preserved_selected_complete_declarations':15241,'full_types_and_standard_axiom_reports':17,'complete_type_and_hidden_boundary_output_matches_historical':True,
       'reused_validation':'Port18VALIDATE helper002, rejection004 (seven rejected classes, exact valid/dependent consumer, disposable environments), Domain005/Prepare006/Driver007/Accounting008; source/object hashes checked now; historical audit028 never promoted.',
       'retained_assumptions':'OtherBudgets R; base/R/B/other/adapter/source/SDK/primitives/StoredCarrierBinding/NativeBindings/native/release. No premise changes or compatibility premise. Bounds 1161+R, Q+1161+R, Q+2322+2R.',
       'limits':'Port17 mixed-cache evidence WITHHELD; no untouched original textual-module replay, external source/IR/native/ELF identity, zeroR, native RO absence, or deployed/release claim. Both deployed targets not yet established.',
       'next_actual_producer':'delegated op3 native source/effect/count, then residual R producers'}
  (E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
  print(json.dumps({k:out[k] for k in ['status','new_charged','cumulative_charged','cumulative_actual_lean','cumulative_pre_lean','remaining']}))
