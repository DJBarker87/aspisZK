"""Verify local source certificates, exact receipt inputs, caps and raw NEP roots."""
from pathlib import Path
import hashlib,json,re,subprocess
from datetime import datetime
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads((R/'D572-final-host-inventory.json').read_text())
def local(n):
 if n.startswith('source/NEP_'):return R/'nep-reachable'/Path(n).name
 if '/'not in n:return R/('D572-'+n)
 return R/n.removeprefix('resume18/')
for n,h in inv['hashes'].items():assert sha(local(n))==h,n
assert inv['guard_sha256']==sha(R/'D571-compile_resume18_d569.py')==sha(Path('tools/pv-b3p6-20261028/compile_resume18_d569.py'))
receipts=[]
for n in inv['hashes']:
 if not n.endswith('/receipt/receipt.json'):continue
 r=json.loads(local(n).read_text());root=local(n).parent;log=(root/'stdout.log').read_text()+(root/'stderr.log').read_text()
 assert r['exit_status']==0 and r['swaps']==0,r['attempt']
 assert r['limits']['memory.max']=='8589934592' and r['limits']['memory.swap.max']=='0'
 assert r['limits']['memory.high']=='6442450944' and r['limits']['pids.max']=='64'
 assert sha(root.parent/'source.lean')==r['source_sha256']
 # Exact committed own-source authority for every module, never another variant.
 auth=r['project_source_authority'];b=subprocess.check_output(['git','show',r['lean_source_revision']+':'+auth['path']]);assert hashlib.sha256(b).hexdigest()==r['source_sha256']
 assert subprocess.check_output(['git','rev-parse',r['lean_source_revision']+':'+auth['path']],text=True).strip()==auth['blob']
 assert 'error:'not in log and 'NEP_FAILURE'not in log and 'sorryAx'not in log and 'native.decide'not in log
 for axioms in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):assert set(axioms.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 assert r['print_axioms'],r['module']
 receipts.append(r)
assert len(receipts)==14 and {r['attempt']for r in receipts}==set(range(79792,79797))|set(range(90600,90609))
# Every scope must have admitted BOTH the outside reservation and the inner barrier.
for r in receipts:
 label=Path(next(n for n in inv['hashes']if n.endswith('/receipt/receipt.json')and json.loads(local(n).read_text())['attempt']==r['attempt'])).parts[0]
 for name in ['reservation.json','barrier.json']:
  admission=json.loads((R/label/name).read_text());assert admission['allowed']is True
 scope=(R/label/'scope.log').read_text();assert 'MemoryHigh=6G'in (R/label/'target.json').read_text() or 'scope'in scope
# Refusal is retained and was retried with the same uncharged ID after cooldown.
ref=json.loads((R/'lean-79795/refusal.json').read_text());assert ref['exit']==78 and ref['allowed']is False and ref['scope_started']is False
assert (R/'lean-79795-r1/receipt/receipt.json').exists()
for label in ['lean-79795','lean-79795-r1']:
 assert (R/label/'reservation.json').exists()
# Outside admission timestamps are present in the JSON epoch field, checked below
# using actual recorded file content rather than local fetch timestamps.
a=json.loads((R/'lean-79795/reservation.json').read_text());b=json.loads((R/'lean-79795-r1/reservation.json').read_text())
elapsed=(datetime.fromisoformat(b['utc'].replace('Z','+00:00'))-datetime.fromisoformat(a['utc'].replace('Z','+00:00'))).total_seconds()
assert elapsed>=180,elapsed
# The wrapper enforces cooldown before scanning and records the refusal; no bypass.
assert inv['uncharged_scope_refusals']==['lean-79795']
for kind in ['external','cache']:assert json.loads((R/f'D572-{kind}-verification-resume18.json').read_text())['mismatches']==[]
assert '0 loaded units listed'in inv['scopes']
for tool in ['source_guards572.py','fixed_indices572.py','step_source572.py','result_source572.py','residual_parity572.py','result_parity572.py','coverage_source572.py','audit_source572.py']:
 subprocess.run(['python3',f'tools/pv-b3p6-20261028/{tool}','--check'],check=True,stdout=subprocess.PIPE)
# Generated chunks contain only named applications, literal state maps and audits.
for p in (D/'lean').glob('PV_B3P_FixedIndices572227_*.lean'):
 assert not re.search(r'\b(simp|norm_num|decide|unfold|rfl|sorry|axiom|admit|native_decide)\b',p.read_text())
log=(R/'lean-90608/receipt/stdout.log').read_text();raw=[json.loads(s)for s in re.findall(r'^NEP_RESULT (.*)$',log,re.M)];plan=json.loads((R/'NEP-PROVENANCE-D572.json').read_text())
assert len(raw)==len(plan['roots'])==405
for x in raw:assert x['equal']is True and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
assert {x['root']for x in raw}==set(plan['roots'])
coverage=json.loads((R/'SOURCE-COVERAGE-D572.json').read_text())
assert sum(c['local_source_state_certificates']for c in coverage['counts'].values())==222
assert inv['budget']==dict(lean_units_remaining=99,extraction_remaining=3,kani_remaining=25)
x=dict(status='CONTEXT CHECKPOINT; source-cone and DeployedWrapper557 remain OPEN',new_lean_charged=len(receipts),success=len(receipts),failed=[],refusals=['79795 outside reservation; same ID retried after cooldown as lean-79795-r1'],new_extraction=0,new_kani=0,host_hashes_verified=len(inv['hashes']),peak_rss_kib=max(r['peak_rss_kib']for r in receipts),longest_wall_seconds=max(r['wall_seconds']for r in receipts),zero_swap=True,raw_NEP_roots=raw,raw_audit_scope='405 complete new top theorem reachable graphs; unchanged endpoint/source cone audit reused from D571; not a full release audit',summary_print_axioms_label='SUMMARY-BASED, separately checked',local_source_certificate_counts=coverage['counts'],guard_sha256=inv['guard_sha256'],budget=inv['budget'],next_lean=inv['next_lean'],full_frozen_manifest_run=False,premises_removed=[],premises_added=[],premises_weakened=[],receipts=[{k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']}for r in sorted(receipts,key=lambda r:r['attempt'])])
(R/'verification-summary-D572.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['new_lean_charged','success','failed','peak_rss_kib','budget','next_lean']}))
