"""Validate exact receipts, trusted axioms, source parity and remaining premises."""
from pathlib import Path
import json,hashlib,lzma,re,subprocess
R=Path('evidence/pv-b3p6-20261028/resume18');sha=lambda b:hashlib.sha256(b).hexdigest()
inv=json.loads((R/'D559-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/');b=p.read_bytes()if p.exists()else lzma.decompress(p.with_name(p.name+'.xz').read_bytes());assert sha(b)==h,n
accepted={};rows=[]
for p in R.glob('lean-797*/receipt/receipt.json'):
 r=json.loads(p.read_text())
 if r['attempt']<79732:continue
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0 and r['shared_sources_written']is False
 assert sha((p.parent.parent/'source.lean').read_bytes())==r['source_sha256']
 assert sha(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']]))==r['source_sha256']
 assert json.loads((p.parent.parent/'reservation.json').read_text())['allowed']is True
 assert json.loads((p.parent.parent/'barrier.json').read_text())['allowed']is True
 log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text()
 if r['exit_status']==0:
  assert 'error:'not in log and 'sorryAx'not in log
  bad=[x for x in re.findall(r'depends on axioms: \[([^\]]*)\]',log) if not set(x.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}]
  if bad:
   assert r['attempt']in [79741,79751,79758,79760] and all('native.decide'in x for x in bad),(r['attempt'],bad)
  else: accepted[r['module']]=r
 rows.append({k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']})
assert len(rows)==32 and sum(r['exit_status']==0 for r in rows)==20
for p in R.glob('N791*/receipt/receipt.json'):
 if int(p.parent.parent.name[1:])<79168:continue
 r=json.loads(p.read_text());assert r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
log=(R/'lean-79765/receipt/stdout.log').read_text();assert len(re.findall(r'depends on axioms: \[',log))==12
assert 'DeployedWrapper557 base ops'in log and 'native.decide'not in log
raw=(R/'lean-79743/receipt/stdout.log').read_text();assert '_native.decide.ax_2'in raw
normalized=(R/'lean-79750/receipt/stdout.log').read_text();assert 'native.decide'not in normalized and 'sorryAx'not in normalized
x=json.loads((R/'STD-SOURCE-IDENTITY-D559.json').read_text());assert x['spec_nth']['token_identical']
for r in x['files']:assert sha(lzma.decompress(Path(r['local_path']).read_bytes()))==r['sha256']
assert json.loads((R/'DRAIN-SOURCE-PARITY-D559.json').read_text())['non_zst_arm_token_identical']
assert json.loads((R/'NTH-PROOF-NORMALIZATION-D559.json').read_text())['exact_transformation_checked']
assert inv['budget']==dict(lean_remaining=36,extraction_remaining=7,kani_remaining=25)
assert inv['next_lean']==79766 and inv['new_native_receipts']==15 and inv['new_kani']==0
assert inv['retired_unsubmitted_lean']==[79749] and [r['attempt']for r in inv['refused']]==[79742]
assert '0 loaded units listed'in inv['scopes']
out=dict(target='NOT ESTABLISHED; DeployedWrapper557 base ops and exact selected_callback remain OPEN',before=dict(changed_associations=36,partial_source_control_entries=9,bridge='UNDISCHARGED'),after=dict(changed_associations=36,partial_source_control_entries=13,default_usize_nth='kernel-normalized extraction/source-control equality; arbitrary message/handler independence',array_helpers='read/prefix-borrow/copy control equality; cast and pointer realization OPEN',drain='six non-ZST source-arm parity checks; pointer/drop association OPEN',bridge='UNDISCHARGED'),receipts=sorted(rows,key=lambda r:r['attempt']),new_lean_charged=32,lean_zero=20,lean_failed=sorted(r['attempt']for r in rows if r['exit_status']!=0),quarantined_scope_results=[79740,79741,79751,79758,79760],new_extraction=15,extraction_zero=7,new_kani=0,budget=inv['budget'],next_lean=79766,unused_lean_slots=34,uncharged_retired=[79742,79749],unused_audit_ids=[79797,79798,79799],peak_lean_rss_kib=max(r['peak_rss_kib']for r in rows),longest_lean_wall_seconds=max(r['wall_seconds']for r in rows),host_hashes_verified=len(inv['hashes']),integrated_axioms='12 outputs, standard-only; no native_decide or sorryAx in the kernel cohort',guard_sha256=inv['guard_sha256'],full_frozen_manifest='NOT run: source-cone incomplete',premises_removed=[],premises_added=[],premises_weakened=[],checkpoint='context checkpoint, not budget exhaustion')
(R/'verification-summary-D559.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['target','new_lean_charged','lean_zero','new_extraction','budget','host_hashes_verified','peak_lean_rss_kib']}))
