"""Verify WIP receipts/cooldowns; do not credit uncompiled family assertions."""
from pathlib import Path
from datetime import datetime
import hashlib,json,re,subprocess
R=Path('evidence/pv-b3p6-20261028/resume18');inv=json.loads((R/'D581-wip-host-inventory.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def local(n):return R/(('D581-'+n)if'/'not in n else n.removeprefix('resume18/'))
for n,h in inv['hashes'].items():assert sha(local(n))==h,n
for label in inv['refusals']:
 p=R/label;ref=json.loads((p/'refusal.json').read_text());assert ref['exit']==78 and ref['allowed']is False and ref['scope_started']is False;assert not(p/'receipt/receipt.json').exists()
for sequence in [['lean-90631','lean-90631-r1','lean-90631-r2','lean-90631-r3','lean-90631-r4'],['lean-90633','lean-90633-r1','lean-90633-r2']]:
 times=[datetime.fromisoformat(json.loads((R/x/'reservation.json').read_text())['utc'])for x in sequence]
 assert all((b-a).total_seconds()>=180 for a,b in zip(times,times[1:])),sequence
receipts=[]
for label in ['lean-90631-r4','lean-90632']:
 p=R/label;r=json.loads((p/'receipt/receipt.json').read_text());assert sha(p/'source.lean')==r['source_sha256']and r['swaps']==0
 assert r['limits']['memory.max']=='8589934592'and r['limits']['memory.high']=='6442450944'and r['limits']['memory.swap.max']=='0'and r['limits']['pids.max']=='64'
 for name in ['reservation','barrier']:assert json.loads((p/(name+'.json')).read_text())['allowed']is True
 auth=r['project_source_authority'];b=subprocess.check_output(['git','show',r['lean_source_revision']+':'+auth['path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 log=(p/'receipt/stdout.log').read_text()
 if r['exit_status']==0:
  assert'sorryAx'not in log and'error:'not in log
  for ax in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):assert set(ax.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 receipts.append(r)
assert receipts[0]['source_sha256']!=receipts[1]['source_sha256']and receipts[0]['exit_status']==1 and receipts[1]['exit_status']==0
assert inv['budget']['lean_units_remaining']==75 and inv['pending_retry_id']==90633
x=dict(status='WIP/PREPARATION; additional source certificates NOT CREDITED pending family compiles and raw24-root audit',host_hashes_verified=len(inv['hashes']),new_charged=2,success=1,failed=[90631],uncharged_refusals=inv['refusals'],cooldowns_at_least180_seconds=True,pending_retry_id=90633,budget=inv['budget'],audited_coverage=357,prepared_uncredited_coverage=365,raw_new24_audit_run=False,print_axioms='SUMMARY-BASED only for accepted generic579; raw audit pending',peak_rss_kib=max(r['peak_rss_kib']for r in receipts),zero_swap=True,premises_removed=[],premises_added=[],premises_weakened=[],receipts=[{k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']}for r in receipts])
(R/'verification-wip-D581.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['host_hashes_verified','new_charged','success','failed','peak_rss_kib','pending_retry_id','budget']}))
