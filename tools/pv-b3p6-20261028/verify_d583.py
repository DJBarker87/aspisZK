"""Verify source pins, both admissions, cooldowns, caps, and full requested NEP walks."""
from pathlib import Path
from datetime import datetime
import hashlib,json,re,subprocess
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();inv=json.loads((R/'D583-host-inventory.json').read_text())
def local(n):
 if n.startswith('source/NEP_'):return R/'nep-reachable'/Path(n).name
 if '/'not in n:return R/('D583-'+n)
 return R/n.removeprefix('resume18/')
for n,h in inv['hashes'].items():assert sha(local(n))==h,n
assert sha(R/'D583-compile_resume18_d569.py')==sha(R/'D581-compile_resume18_d569.py')==sha(Path('tools/pv-b3p6-20261028/compile_resume18_d569.py'))
receipts=[]
for n in inv['hashes']:
 if not n.endswith('/receipt/receipt.json'):continue
 r=json.loads(local(n).read_text());root=local(n).parent;r['_label']=root.parent.name;log=(root/'stdout.log').read_text()+(root/'stderr.log').read_text();assert r['swaps']==0
 assert r['limits']==dict(r['limits'],**{'memory.max':'8589934592','memory.high':'6442450944','memory.swap.max':'0','pids.max':'64'})
 assert sha(root.parent/'source.lean')==r['source_sha256']
 auth=r['project_source_authority'];rev=r['lean_source_revision'];b=subprocess.check_output(['git','show',rev+':'+auth['path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',rev+':'+auth['path']],text=True).strip()==auth['blob']
 if r['exit_status']==0:
  assert 'error:'not in log and 'NEP_FAILURE'not in log and 'sorryAx'not in log
  for ax in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):assert set(ax.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 else:assert r['exit_status']==1 and 'error:'in log
 for name in ['reservation.json','barrier.json']:assert json.loads((root.parent/name).read_text())['allowed']is True
 receipts.append(r)
for r in receipts:
 if r['exit_status']!=0:
  later=[s for s in receipts if s['module']==r['module']and s['attempt']>r['attempt']];assert later and all(s['source_sha256']!=r['source_sha256']for s in later)
for label in inv['refusals']:
 p=R/label;f=json.loads((p/'refusal.json').read_text());assert f['exit']==78 and f['allowed']is False and f['scope_started']is False and not(p/'receipt/receipt.json').exists()
# Every retry respects the previous refusal's real admission timestamp.
for attempt in [90633,90638]:
 dirs=sorted((p for p in R.glob(f'lean-{attempt}*')if p.is_dir()),key=lambda p:0 if p.name==f'lean-{attempt}'else int(p.name.split('-r')[1])+1)
 for prev,next_ in zip(dirs,dirs[1:]):
  if(prev/'refusal.json').exists():
   a=datetime.fromisoformat(json.loads((prev/'reservation.json').read_text())['utc']);b=datetime.fromisoformat(json.loads((next_/'reservation.json').read_text())['utc']);assert(b-a).total_seconds()>=180,(prev,next_)
assert '0 loaded units listed'in inv['scopes']
for kind in ['external','cache']:assert json.loads((R/f'D583-{kind}-verification-resume18.json').read_text())['mismatches']==[]
tools=['index_cursor579','metadata_source580','coverage_source579','coverage_source580','audit_source580','normalized_indices583','computed_indices583','metadata_indices584','callback_indices584','coverage_source584','audit_source583']
for tool in tools:subprocess.run(['python3',f'tools/pv-b3p6-20261028/{tool}.py','--check'],check=True,stdout=subprocess.PIPE)
for pattern in ['NormalizedIndices583227*','ComputedIndices583227','MetadataIndices584227','CallbackIndices584227']:
 for p in(D/'lean').glob(f'PV_B3P_{pattern}.lean'):assert not re.search(r'\b(simp|norm_num|decide|unfold|rfl|sorry|axiom|admit|native_decide)\b',p.read_text()),p
raws=[]
for cohort in [580,583]:
 plan=json.loads((R/f'NEP-PROVENANCE-D{cohort}.json').read_text());module=plan['driver'];runs=[r for r in receipts if r['module']==module and r['exit_status']==0];assert len(runs)==1
 label=runs[0]['_label'];log=(R/label/'receipt/stdout.log').read_text();raw=[json.loads(s)for s in re.findall(r'^NEP_RESULT (.*)$',log,re.M)]
 assert len(raw)==len(plan['roots'])and{r['root']for r in raw}==set(plan['roots'])
 for row in raw:assert row['equal']is True and set(row['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
 raws+=raw
coverage=json.loads((R/'SOURCE-COVERAGE-D584.json').read_text());assert sum(v['local_source_state_certificates']for v in coverage['counts'].values())==459
assert inv['budget']['lean_units_remaining']==280-inv['lean_attempts']
x=dict(status='CONTEXT CHECKPOINT; DeployedWrapper557 and privacy target OPEN',new_lean_charged=len(receipts),success=sum(r['exit_status']==0 for r in receipts),failed=[r['attempt']for r in receipts if r['exit_status']!=0],uncharged_refusals=inv['refusals'],new_extraction=0,new_kani=0,host_hashes_verified=len(inv['hashes']),peak_rss_kib=max(r['peak_rss_kib']for r in receipts),longest_wall_seconds=max(r['wall_seconds']for r in receipts),zero_swap=True,raw_NEP_roots=raws,raw_audit_scope='24 previously prepared and97 new top theorem complete reachable graphs; unchanged endpoint/source-cone graphs reuse D571; not a full release replay',print_axioms_label='SUMMARY-BASED, checked separately',local_source_certificate_counts=coverage['counts'],guard_sha256=sha(R/'D583-compile_resume18_d569.py'),budget=inv['budget'],next_lean=inv['numerical_next_unused_id'],full_frozen_manifest_run=False,premises_removed=[],premises_added=[],premises_weakened=[],deterministic_checks=tools,receipts=[{k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']}for r in sorted(receipts,key=lambda r:r['attempt'])])
(R/'verification-summary-D583.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['new_lean_charged','success','failed','peak_rss_kib','budget','next_lean']}))
