"""Collect exact-source accepted receipts, rejected evidence, and unchanged deployed ledger."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();BASE='bd9014f8833e9319fe6fda3d94fdb6546c7f2bb0'
rows=[]
for f in sorted(P.glob('JFu12_*/receipt.json')):
 r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R));r['errors']=[l for l in f.with_name('stdout.log').read_text().splitlines() if 'error:' in l or 'error(' in l];rows.append(r)
assert len(rows)==100
(P/'JFu_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
files=subprocess.check_output(['git','diff','--name-only',BASE,'--','lean'],cwd=R,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard','lean'],cwd=R,text=True).splitlines()
valid={}
for rel in dict.fromkeys(files):
 f=R/rel
 if not f.exists() or f.suffix!='.lean':continue
 assert f.name.startswith('JFu_'),f
 h=sha(f.read_bytes());matches=[r for r in rows if r['exit_status']==0 and r.get('source_hashes',{}).get(f.name)==h];assert matches,f
 r=matches[-1]
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  if 'depends on axioms:' in line:
   axioms=line.split('depends on axioms:',1)[1].strip().strip('[]');assert {x.strip() for x in axioms.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},line
 valid[f.name]=dict(sha256=h,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFu_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
final=rows[-1];assert final['attempt']=='JFu12_100' and final['exit_status']==0
out=(P/'JFu12_100/stdout.log').read_text();before=(P/'JFu_BEFORE_Rc10_Top.lean.txt').read_bytes();after=(R/'lean/Rc10_Top.lean').read_bytes();assert before==after
(P/'JFu_AFTER_Rc10_Top.lean.txt').write_bytes(after)
start=out.index('theorem AspisR1.Rc10_Top.deployed');stop=out.index("'AspisR1.Rc10_Top.deployed' depends on axioms:")
(P/'JFu_AFTER_Rc10_KERNEL.txt').write_text(out[start:stop])
start=out.index('theorem AspisR1.JFu_PartialFixture.inhabited');stop=out.index("'AspisR1.JFu_PartialFixture.inhabited' depends on axioms:")
(P/'JFu_PARTIAL_FIXTURE_KERNEL.txt').write_text(out[start:stop])
(P/'JFu_BEFORE_PARTIAL_FIXTURE.lean.txt').write_bytes((R/'lean/JFm_ChallengeFixture.lean').read_bytes())
(P/'JFu_AFTER_PARTIAL_FIXTURE.lean.txt').write_bytes((R/'lean/JFu_PartialFixture.lean').read_bytes())
old=json.loads((P/'JFu12_002/receipt.json').read_text())['deps_fingerprint']['selected_objects']['Rc10_Top.olean'];new=final['deps_fingerprint']['selected_objects']['Rc10_Top.olean'];assert old['sha256']==new['sha256']
counts=dict(T=89,P=16,G=13,C=0);zero=dict(T=0,P=0,G=0,C=0)
ledger=dict(target='AspisR1.Rc10_Top.deployed',method='design/PREMISE-LEDGER-20261025.md quantified atomic-law families (Recount on Rc7 method, applied to Rc10): conjunction leaves, guards and shared witnesses; deployment rows included; L185 aliases L159; native/global families stay distinct',before=counts,after=counts,actual_distinct=dict(T=83,P=12,G=13,C=0),deployment_non_alias=dict(T=6,P=4,G=0,C=0),removed=zero,added=zero,changed=zero,before_source_sha256=sha(before),after_source_sha256=sha(after),source_statements_identical=True,before_object=old,after_object=new,target_object_hash_unchanged=True,kernel_prints_identical=(P/'JFu_BEFORE_Rc10_KERNEL.txt').read_bytes()==(P/'JFu_AFTER_Rc10_KERNEL.txt').read_bytes(),limitations='No deployed premise removed. Joint partial real-byte source non-vacuity does not imply full terminal or native wrapper acceptance. No quantifier, carrier, failure event, work metric, game, constant or approved trust item changed.')
(P/'JFu_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
summary=dict(charged=100,lean_processes=100,passes=sum(r['exit_status']==0 for r in rows),rejects=sum(r['exit_status']!=0 for r in rows),kani=0,validated_modules=len(valid),wall_seconds=sum(r['wall_seconds'] for r in rows),max_reported_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),final=final,measurement_note='Per-receipt GNU-time RSS is reported as observed; cgroup peak is separate. No full descendant RSS is inferred for voluntarily stopped014.',source_statements_identical=True,target_object_hash_unchanged=True)
(P/'JFu_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k not in ['final']})
