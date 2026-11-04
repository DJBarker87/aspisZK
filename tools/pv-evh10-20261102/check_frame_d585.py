"""Focused D585 source/receipt certificate. No compilation or release audit."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
# Reuse the immutable adopted disassembly and the corrected six-push arithmetic.
r=subprocess.run([sys.executable,'tools/pv-evh10-20261102/check_stack_resource_d583.py','--check'],capture_output=True,text=True)
assert r.returncode==0,r.stderr+r.stdout
binary=json.loads((E/'binary-correspondence-D581.json').read_text())
assert sha((E/'out-N91601.log').read_bytes())==binary['analysis_sha256']
modules=['PV_EVH_PhysicalFrame','PV_EVH_FrameTransitions','PV_EVH_FrameSource','PV_EVH_FrameWorld']
rows=[json.loads(p.read_text()) for p in E.glob('receipt-*.json') if p.stem.split('-')[-1].isdigit() and 90259<=int(p.stem.split('-')[-1])<=90296]
rows.sort(key=lambda r:r['attempt'])
assert [r['attempt'] for r in rows]==list(range(90259,90259+len(rows)))
accepted={}
for r in rows:
 a=r['attempt'];raw=subprocess.check_output(['git','show',r['source_revision']+':'+r['source_path']])
 assert sha(raw)==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',r['source_revision']+':'+r['source_path']],text=True).strip()==r['source_git_blob']
 assert r['admission']['allowed'] is True
 assert all(s in r['command'] for s in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64','7000'])
 out=(E/f'out-{a}.log').read_text();tim=(E/f'time-{a}.log').read_text()
 assert f"Exit status: {r['exit']}" in tim and r['wall']
 assert r['swaps']=='0' and int(r['peak_rss_kbytes'])<8*1024*1024
 assert json.loads((E/f'transport-{a}.json').read_text())['exit']==int(r['exit'])
 if r['accepted']:
  assert r['exit']=='0' and 'sorryAx' not in out and 'error:' not in out
  assert raw==Path(r['source_path']).read_bytes()
  assert len(re.findall(r'^theorem ',raw.decode(),re.M))==len(r['axioms'])
  for line in r['axioms']:
   if 'depends on axioms:' in line:
    axioms=line.split('depends on axioms: [')[1].split(']')[0].replace('\n','').replace(' ','').split(',')
    assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
  accepted[r['target']]=a
assert set(accepted)==set(modules)
for m in modules:
 source=Path('lean/'+m+'.lean').read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom ',source,re.M)
 assert 'maxHeartbeats' not in source and 'maxRecDepth' not in source
physical=Path('lean/PV_EVH_PhysicalFrame.lean').read_text()
assert '| .mask i => 304 + 336*i.val' in physical
assert '| .result i => 352 + 336*i.val' in physical
assert 'structure Frame where' in physical and 'structure Grant' in physical
for field in ['slotTable','offsets','lifetimes','activeFrames','request','answer']:
 assert re.search(r'^  '+field+r' :',physical,re.M)
source=Path('lean/PV_EVH_FrameSource.lean').read_text()
assert '(ActualEntropyEntryPrefix : Type)' in source
assert 'opsNative (rawBase base) heap box ops' in source
assert 'structure OWNER' not in source
world=Path('lean/PV_EVH_FrameWorld.lean').read_text()
assert 'r.after,r.events,resourceOutcome' in world
assert 'PV_EVH_EntropyRejectDelivery.completed q.activation q.sp d q.state' in world
inputs=['evidence/pv-evh10-20261102/'+x for x in ['PHYSICAL-D581.md','STACK-RESOURCE-D583.md','BLOCKER-D584.md','FRAME-ENTRY-D583.md','binary-correspondence-D581.json','out-N91601.log']]
result=dict(evidence_class='binary-structural (adopted binary), plus V370 compiler-cohort',
 adopted_binary_sha256='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0',
 inputs={p:sha(Path(p).read_bytes()) for p in inputs},
 sources={m:sha(Path('lean/'+m+'.lean').read_bytes()) for m in modules},
 accepted=accepted,failed=[r['attempt'] for r in rows if not r['accepted']],
 receipts=[{k:r[k] for k in ['attempt','target','source_revision','source_sha256','exit','wall','peak_rss_kbytes','swaps','accepted','axioms']} for r in rows],
 axioms_mode='SUMMARY-BASED; no raw/full-data coherence claim',
 actual_prefix_domain_constructed=False,correspondence_instantiated=False,
 owner_defined=False,endpoint_rows_removed=[],new_trust_fields=[],native_runs=0,
 next_lean=90259+len(rows),next_native='N91603',
 guard_sha256=sha(Path('tools/pv-evh10-20261102/compile.py').read_bytes()))
out=E/'frame-D585.json'
if '--check' in sys.argv:
 assert json.loads(out.read_text())==result
 print('PASS D585 frame source and receipts; actual-prefix producer remains uninstantiated')
else:
 out.write_text(json.dumps(result,indent=2)+'\n')
 print('WROTE',out)
