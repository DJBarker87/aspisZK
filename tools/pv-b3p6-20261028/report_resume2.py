"""Check exact receipts, axioms, source revisions and final private closure."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path('evidence/pv-b3p6-20261028');R=D/'receipts-resume2';base='1e826627aa39fe02569bf840efb894eaa287efcf'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],stderr=subprocess.DEVNULL).decode().strip()
t=json.loads((R/'TALLY-resume2.json').read_text());assert t['lean_attempts']==100 and t['kani_runs']==0
assert sorted(t['used_ids'])==list(range(50500,50600))
assert t['audit_ids_used']==[50597,50598,50599]
(D/'TALLY-resume2.json').write_text(json.dumps(t,indent=2)+'\n')
rows=[];full=[];corrections=[]
for p in sorted(R.glob('lean-*/receipt/receipt.json')):
 r=json.loads(p.read_text());full.append((p,r))
 assert sha(p.parent.parent/'source.lean')==r['source_sha256']
 stdout=(p.parent/'stdout.log').read_text();stderr=(p.parent/'stderr.log').read_text()
 axioms=[]
 for value in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',stdout+stderr):axioms+=value.replace('\n',' ').split(',')
 axioms=sorted({x.strip() for x in axioms if x.strip()})
 if r['exit_status']==0:
  assert 'sorryAx' not in stdout+stderr,p
  assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(p,axioms)
  assert r['swaps']==0
 a=r['project_source_authority'];oldrev=r.get('lean_source_revision','');valid=False
 try:valid=hashlib.sha256(subprocess.check_output(['git','show',oldrev+':'+a['path']],stderr=subprocess.DEVNULL)).hexdigest()==r['source_sha256']
 except subprocess.CalledProcessError:pass
 effective=oldrev
 if not valid:
  candidates=git('log','--format=%H',base+'..HEAD','--',a['path']).splitlines()+[base]
  for rev in candidates:
   try:blob=git('rev-parse',rev+':'+a['path'])
   except subprocess.CalledProcessError:continue
   if blob==a['blob']:
    effective=rev;break
  else:raise AssertionError(('no exact source revision',r['attempt']))
  corrections.append(dict(attempt=r['attempt'],module=r['module'],old_lean_revision_label=oldrev,effective_lean_source_revision=effective,source_blob=a['blob'],source_sha256=r['source_sha256'],original_receipt_unchanged=True,reason='early wrapper inherited prior host proof-revision label; exact h5 source/blob/dependency fingerprints were recorded correctly'))
 fields=['attempt','module','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','swaps','source_sha256','deps_fingerprint','source_revision','lean_source_revision']
 rows.append(dict({k:r.get(k) for k in fields},effective_lean_source_revision=effective,accepted_axioms=axioms,receipt=str(p),proof_credit=r['exit_status']==0))
assert len(rows)==100
(D/'receipt-index-resume2.json').write_text(json.dumps(dict(receipts=rows,failed_drafts_have_no_credit=True,revision_corrections='resume2-revision-corrections.json'),indent=2)+'\n')
(D/'resume2-revision-corrections.json').write_text(json.dumps(corrections,indent=2)+'\n')
resolution=json.loads((D/'project-resolution.json').read_text());manifest=json.loads((D/'resume2-object-manifest.json').read_text());objects={r['path']:r['sha256'] for r in manifest['files']};checked=[];bad=[]
for module,a in resolution['modules'].items():
 good=[(p,r) for p,r in full if r['module']==module and r['source_sha256']==a['sha256'] and r['exit_status']==0]
 assert good,module
 p,r=max(good,key=lambda x:x[1]['attempt'])
 for dep,obj in r['dependency_objects'].items():
  if dep in resolution['modules'] and objects.get(obj['path'])!=obj['sha256']:bad.append(dict(module=module,dependency=dep,recorded=obj,actual=objects.get(obj['path'])))
 checked.append(dict(module=module,source_sha256=a['sha256'],blob=a['blob'],receipt=str(p),object_sha256=objects.get('/home/dombarker/project-offloads/codex-pv-b3p6-20261028/lean-objects/'+module.replace('.','/')+'.olean')))
assert not bad,bad
(D/'closure-hash-audit-resume2.json').write_text(json.dumps(dict(root=resolution['roots'],checked=checked,dependency_mismatches=bad,external_authority='h4; fresh pre-first-compile verification of5673 objects',scope='focused packet, not privacy endpoint release'),indent=2)+'\n')
changed=git('diff','--name-only',base,'HEAD').splitlines();forbidden=[p for p in changed if p.startswith(('crates/','programs/'))];assert not forbidden
source_audit=[]
for p in changed:
 if not p.endswith('.lean') or not p.startswith(str(D/'lean')):continue
 q=Path(p);s=q.read_text();code=re.sub(r'/\*.*?\*/|/-.*?-/', '',s,flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',code),p
 assert not re.search(r'^import\s+XR',code,re.M),p
 options=re.findall(r'^set_option (?:maxRecDepth|maxHeartbeats).*$',code,re.M)
 assert not options or q.name in {'PV_B3P_Types132.lean','PV_B3P_Emission132.lean'},(p,options)
 source_audit.append(dict(path=p,sha256=sha(q),resource_options=options,generated_options_preserved=q.name in {'PV_B3P_Types132.lean','PV_B3P_Emission132.lean'}))
(D/'source-audit-resume2.json').write_text(json.dumps(dict(base=base,forbidden_shipped_source_changes=forbidden,sources=source_audit,forbidden_declarations=[],xr_imports=[],shared_source_writes=False,keys_touched=False),indent=2)+'\n')
print(json.dumps(dict(attempts=100,passed=sum(r['proof_credit'] for r in rows),failed=sum(not r['proof_credit'] for r in rows),closure_modules=len(checked),dependency_mismatches=bad,revision_label_corrections=len(corrections))))
