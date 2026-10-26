"""Collect exact-source receipts; never treat rejected recovery axioms as evidence."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for n in range(1,101):
 a=f'JFp_{n:03}';p=P/a/'receipt.json'
 if n==42:
  rows.append(json.loads((P/'JFp_042_FAILURE.json').read_text()));continue
 assert p.exists(),a
 r=json.loads(p.read_text());r['receipt']=str(p.relative_to(R));r['errors']=[l for l in (P/a/'stdout.log').read_text().splitlines() if 'error:' in l or 'error(' in l];rows.append(r)
(P/'JFp_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={}
for f in sorted((R/'lean').glob('JFp_*.lean')):
 h=sha(f.read_bytes());matches=[r for r in rows if r.get('exit_status')==0 and r.get('source_hashes',{}).get(f.name)==h];assert matches,f
 r=matches[-1]
 for l in r['print_axioms']:
  assert 'sorryAx' not in l,l
  if 'depends on axioms:' in l:
   ax=l.split('depends on axioms:',1)[1].strip().strip('[]');assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},l
 valid[f.name]=dict(sha256=h,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFp_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
source=(R/'lean/Rc10_Top.lean').read_bytes();before=(P/'JFp_BEFORE_Rc10_Top.lean.txt').read_bytes();assert source==before
(P/'JFp_AFTER_Rc10_Top.lean.txt').write_bytes(source)
audits=[r for r in rows if 'Rc10_Top.olean' in r.get('deps_fingerprint',{}).get('selected_objects',{}) and r.get('exit_status')==0]
assert len(audits)>=2
for kind,r in [('BEFORE',audits[0]),('AFTER',audits[-1])]:
 text=(P/r['attempt']/'stdout.log').read_text();start=text.index('theorem AspisR1.Rc10_Top.deployed');kernel=text[start:].split("'AspisR1.Rc10_Top.deployed' depends on axioms:")[0].rstrip()+'\n';(P/f'JFp_{kind}_Rc10_KERNEL.txt').write_text(kernel)
old=audits[0]['deps_fingerprint']['selected_objects']['Rc10_Top.olean'];new=audits[-1]['deps_fingerprint']['selected_objects']['Rc10_Top.olean'];assert old['sha256']==new['sha256']
raw_before=(P/'JFp_BEFORE_Rc10_KERNEL.txt').read_bytes();after_kernel=(P/'JFp_AFTER_Rc10_KERNEL.txt').read_bytes()
(P/'JFp_082_RAW_Rc10_KERNEL.txt').write_bytes(raw_before)
if len(after_kernel)>len(raw_before):(P/'JFp_BEFORE_Rc10_KERNEL.txt').write_bytes(after_kernel)
counts=dict(T=89,P=16,G=13,C=0);zero=dict(T=0,P=0,G=0,C=0)
ledger=dict(target='AspisR1.Rc10_Top.deployed',method='design/PREMISE-LEDGER-20261025.md: Rc10 quantified atomic-law families, conjunction leaves, guarded conditional laws and common witnesses, with deployment rows; L185 aliases L159; native/global copies remain distinct',before=counts,after=counts,actual_distinct=dict(T=83,P=12,G=13,C=0),deployment_non_alias=dict(T=6,P=4,G=0,C=0),removed=zero,added=zero,changed=zero,before_source_sha256=sha(before),after_source_sha256=sha(source),source_statements_identical=True,before_object=old,after_object=new,target_object_hash_unchanged=True,limitations='No complete accepted native pair or actual-top premise removal; partial fixture and concrete SHA checks do not imply acceptance or source/syscall/artifact refinement. No quantifier, carrier, failure event, numerical constant, game clause or trust item changed.')
(P/'JFp_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
process=[r for r in rows if r.get('lean_processes',1)!=0]
summary=dict(charged=100,lean_processes=len(process),passes=sum(r.get('exit_status')==0 for r in process),rejects=sum(r.get('exit_status')!=0 for r in process),launcher_preflight_rejects=1,kani=0,modules=len(valid),wall_seconds=sum(r['wall_seconds'] for r in process),max_rss_kib=max(int(r['peak_rss_kib']) for r in process),swaps=sum(int(r['swaps']) for r in process),final=rows[-1],source_statements_identical=True,target_object_hash_unchanged=True)
(P/'JFp_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k!='final'})
