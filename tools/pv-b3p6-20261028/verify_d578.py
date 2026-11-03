"""Check receipts/source pins/caps/admission and ALL new NEP reachable graphs."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D578-final-host-inventory.json').read_text())
def local(n):
 if n.startswith('source/NEP_'):return R/'nep-reachable'/Path(n).name
 if '/'not in n:return R/('D578-'+n)
 return R/n.removeprefix('resume18/')
for n,h in inv['hashes'].items():assert sha(local(n))==h,n
assert inv['guard_sha256']==sha(R/'D572-compile_resume18_d569.py')==sha(Path('tools/pv-b3p6-20261028/compile_resume18_d569.py'))
receipts=[];success=[];failed=[]
for n in inv['hashes']:
 if not n.endswith('/receipt/receipt.json'):continue
 r=json.loads(local(n).read_text());root=local(n).parent;log=(root/'stdout.log').read_text()+(root/'stderr.log').read_text()
 assert r['swaps']==0 and r['limits']['memory.max']=='8589934592'and r['limits']['memory.swap.max']=='0'
 assert r['limits']['memory.high']=='6442450944'and r['limits']['pids.max']=='64'
 assert sha(root.parent/'source.lean')==r['source_sha256']
 auth=r['project_source_authority'];rev=r['lean_source_revision'];b=subprocess.check_output(['git','show',rev+':'+auth['path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',rev+':'+auth['path']],text=True).strip()==auth['blob']
 assert r['print_axioms'],r['attempt']
 if r['exit_status']==0:
  assert 'error:'not in log and 'NEP_FAILURE'not in log and 'sorryAx'not in log
  for axioms in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):assert set(axioms.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
  success.append(r)
 else:
  assert r['exit_status']==1 and 'error:'in log
  failed.append(r)
 for name in ['reservation.json','barrier.json']:assert json.loads((root.parent/name).read_text())['allowed']is True
 receipts.append(r)
assert {r['attempt']for r in receipts}==set(range(90609,90631))
assert{r['attempt']for r in failed}=={90609,90610,90615,90626,90627}
assert len(success)==17
# All resubmissions after elaboration failure have different source bytes.
for r in failed:
 later=[s for s in receipts if s['module']==r['module']and s['attempt']>r['attempt']]
 assert later and all(s['source_sha256']!=r['source_sha256']for s in later)
assert inv['uncharged_scope_refusals']==[]and'0 loaded units listed'in inv['scopes']
for kind in ['external','cache']:assert json.loads((R/f'D578-{kind}-verification-resume18.json').read_text())['mismatches']==[]
for tool in ['initializer_source578','frame_indices578','slice_source578','dominated_indices578','specialized_indices578','range_indices578','window_indices578','sub_panic_source578','coverage_source578','audit_source578']:
 subprocess.run(['python3',f'tools/pv-b3p6-20261028/{tool}.py','--check'],check=True,stdout=subprocess.PIPE)
# Generated families only apply named lemmas; large numeric normalization is absent.
for pattern in ['InitializerFamily','FrameIndices','SliceFamily','DominatedIndices','SpecializedIndices','RangeIndices','WindowIndices','SubPanicFamily']:
 for p in (D/'lean').glob(f'PV_B3P_{pattern}578227*.lean'):
  assert not re.search(r'\b(simp|norm_num|decide|unfold|rfl|sorry|axiom|admit|native_decide)\b',p.read_text()),p
log=(R/'lean-90630/receipt/stdout.log').read_text();raw=[json.loads(s)for s in re.findall(r'^NEP_RESULT (.*)$',log,re.M)];plan=json.loads((R/'NEP-PROVENANCE-D578.json').read_text())
assert len(raw)==len(plan['roots'])==158
for row in raw:assert row['equal']is True and set(row['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
assert{x['root']for x in raw}==set(plan['roots'])
coverage=json.loads((R/'SOURCE-COVERAGE-D578.json').read_text())
assert sum(v['local_source_state_certificates']for v in coverage['counts'].values())==357
assert inv['budget']==dict(lean_units_remaining=77,extraction_remaining=3,kani_remaining=25)and inv['next_lean']==90631
x=dict(status='CONTEXT CHECKPOINT; DeployedWrapper557 and privacy target remain OPEN',new_lean_charged=len(receipts),success=len(success),failed=[r['attempt']for r in failed],refusals=[],new_extraction=0,new_kani=0,host_hashes_verified=len(inv['hashes']),peak_rss_kib=max(r['peak_rss_kib']for r in receipts),longest_wall_seconds=max(r['wall_seconds']for r in receipts),zero_swap=True,raw_NEP_roots=raw,raw_audit_scope='158 complete new top theorem reachable graphs; unchanged endpoint/source-cone graphs reuse D571; not a full release audit',print_axioms_label='SUMMARY-BASED, checked separately',local_source_certificate_counts=coverage['counts'],guard_sha256=inv['guard_sha256'],budget=inv['budget'],next_lean=inv['next_lean'],full_frozen_manifest_run=False,premises_removed=[],premises_added=[],premises_weakened=[],receipts=[{k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']}for r in sorted(receipts,key=lambda r:r['attempt'])])
(R/'verification-summary-D578.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['new_lean_charged','success','failed','peak_rss_kib','budget','next_lean']}))
