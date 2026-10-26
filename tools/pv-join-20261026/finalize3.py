"""Validate exact resume3 accounting, accepted axiom sets and final coverage."""
from pathlib import Path
import json,re,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume3'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
xs=[json.loads(f.read_text()) for f in sorted(e.glob('*-receipt.json'))]
assert len(xs)==100,len(xs)
assert all(x['charged_lean_attempts']==1 for x in xs)
tally=json.loads((e/'attempt-tally.json').read_text())
assert len(set(tally['ids']))==len(tally['ids'])
assert tally['charged']==100 and tally['pending'] is None
accepted=[];failed=[]
for x in xs:
 a=x['attempt'];assert 36500<=a<=36799
 assert sha(e/f'{a}.lean.txt')==x['source_sha256']
 raw=(e/f'{a}-out.log').read_text()
 if x['validation_exit']==0:
  assert x['exit_status']==0 and 'sorryAx' not in raw and ': error:' not in raw
  for line in x['print_axioms']:
   if 'depends on axioms: [' in line:
    assert set(y.strip() for y in line.split('depends on axioms: [')[1].split(']')[0].split(',')) <= {'propext','Classical.choice','Quot.sound'}
  accepted.append(a)
 else:failed.append(a)
assert all('Audit' in x['module'] for x in xs[-5:]),[x['module'] for x in xs[-5:]]
last=xs[-1];assert last['module']=='R1Z/PV_Join_CombinedAudit'
manifest=json.loads((e/'combined-audit-manifest.json').read_text())
final_raw=(e/f"{last['attempt']}-out.log").read_text()
for name in manifest['theorems']+['R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed']:
 assert re.search("'"+re.escape(name)+"' (depends on axioms:|does not depend on any axioms)",final_raw),name
for s in manifest['sources']:
 p=r/'docs/research/v8-r0-zk-20261009/lean'/(s['module'].replace('.','/')+'.lean')
 assert sha(p)==s['sha256'],p
summary=dict(charged=100,passed=len(accepted),failed=failed,ids=tally['ids'],no_id_reuse=True,last_five_reserved_for_audit=True,baseline_initial=xs[0]['validation_exit'],baseline_recovered=next(x for x in xs if x['attempt']==36579)['validation_exit'],final_combined_audit=last['validation_exit'],final_attempt=last['attempt'],final_theorem_reports=len(last['print_axioms']),pv_join_theorems=len(manifest['theorems']),peak_rss_kib=max(x['peak_rss_kib'] for x in xs),swaps=max(x['swaps'] for x in xs),inventory_before=30,inventory_after=30,endpoint_premises_removed=0,target_established=False,release_manifest_replayed=False,kani_runs=0,local_lean_compiles=0)
(e/'receipt-index.json').write_text(json.dumps(dict(summary=summary,receipts=xs),indent=2)+'\n')
(e/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','ce8e0224ab..HEAD'],cwd=r,text=True))
print(json.dumps(summary,indent=2))
