"""Collect exact-current-source validation and the unchanged actual-top ledger.
Rejected attempts, including the accidental unchanged062, remain charged.
"""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for n in range(1,101):
 a=f'JFr_{n:03}';f=P/a/'receipt.json';assert f.exists(),a
 r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R))
 r['errors']=[l for l in (P/a/'stdout.log').read_text().splitlines() if 'error:' in l or 'error(' in l]
 rows.append(r)
(P/'JFr_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={}
for f in sorted((R/'lean').glob('JFr_*.lean')):
 h=sha(f.read_bytes());matches=[r for r in rows if r['exit_status']==0 and r.get('source_hashes',{}).get(f.name)==h]
 assert matches,f
 r=matches[-1]
 for l in r['print_axioms']:
  assert 'sorryAx' not in l,l
  if 'depends on axioms:' in l:
   ax=l.split('depends on axioms:',1)[1].strip().strip('[]')
   assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},l
 valid[f.name]=dict(sha256=h,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFr_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
source=(R/'lean/Rc9_Top.lean').read_bytes();before=(P/'JFr_BEFORE_Rc9_Top.lean.txt').read_bytes()
(P/'JFr_AFTER_Rc9_Top.lean.txt').write_bytes(source)
old=rows[0]['deps_fingerprint']['selected_objects']['Rc9_Top.olean'];new=rows[-1]['deps_fingerprint']['selected_objects']['Rc9_Top.olean']
for name,r in [('BEFORE',rows[0]),('AFTER',rows[-1])]:
 stdout=(P/r['attempt']/'stdout.log').read_text();start=stdout.index('theorem AspisR1.Rc9_Top.deployed')
 kernel=stdout[start:].split("'AspisR1.Rc9_Top.deployed' depends on axioms:")[0].rstrip()+'\n'
 (P/f'JFr_{name}_Rc9_KERNEL.txt').write_text(kernel)
counts=dict(T=89,P=22,G=13,C=0)
ledger=dict(target='AspisR1.Rc9_Top.deployed',method='design/PREMISE-LEDGER-20261025.md: Rc9 quantified atomic-law families, conjunction leaves, guards and shared witnesses; deployment rows included; L185 aliases L159, L137 duplicates L134; native/global domains remain distinct',before=counts,after=counts,actual_distinct=dict(T=83,P=18,G=13,C=0),deployment_non_alias=dict(T=6,P=4,G=0,C=0),raw_non_alias_combined=dict(T=89,P=23,G=13,C=0),removed=dict(T=0,P=0,G=0,C=0),added=dict(T=0,P=0,G=0,C=0),changed=dict(T=0,P=0,G=0,C=0),source_statements_identical=source==before,before_source_sha256=sha(before),after_source_sha256=sha(source),before_object=old,after_object=new,target_object_hash_unchanged=old['sha256']==new['sha256'],limitations='No complete accepted native pair or joint release-premise inhabitation. Local concrete decoder/arithmetic proofs do not remove actual deployed premises. Trust/game/quantifiers/carriers/failure event/numeric constants unchanged.')
assert ledger['source_statements_identical'] and ledger['target_object_hash_unchanged']
(P/'JFr_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
summary=dict(charged=100,lean_processes=100,passes=sum(r['exit_status']==0 for r in rows),rejects=sum(r['exit_status']!=0 for r in rows),kani=0,modules=len(valid),wall_seconds=sum(r['wall_seconds'] for r in rows),max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),final=rows[-1],workflow_exception='062 accidentally repeated unchanged rejected061; rejected and charged, not accepted validation. No timeout or memory-kill rerun.',source_statements_identical=True,target_object_hash_unchanged=True)
(P/'JFr_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k!='final'})
