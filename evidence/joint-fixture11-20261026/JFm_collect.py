"""Collect exact-source checks, rejected diagnostics, and unchanged deployed ledger."""
from pathlib import Path
import hashlib,json,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for f in sorted(P.glob('JFm_*/receipt.json')):
 r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R));r['errors']=[l for l in f.with_name('stdout.log').read_text().splitlines() if 'error:' in l or 'error(' in l];rows.append(r)
(P/'JFm_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={}
for f in sorted((R/'lean').glob('JFm_*.lean')):
 h=sha(f.read_bytes());matches=[r for r in rows if r['exit_status']==0 and r.get('source_hashes',{}).get(f.name)==h];assert matches,f
 r=matches[-1]
 for l in r['print_axioms']:
  assert 'sorryAx' not in l,l
  if 'depends on axioms:' in l:
   ax=l.split('depends on axioms:',1)[1].strip().strip('[]');assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},l
 valid[f.name]=dict(sha256=h,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFm_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
before=(P/'JFm_BEFORE_Rc10_Top.lean.txt').read_bytes();source=(R/'lean/Rc10_Top.lean').read_bytes();assert source==before
(P/'JFm_AFTER_Rc10_Top.lean.txt').write_bytes(source)
audits=[r for r in rows if 'Rc10_Top.olean' in r.get('deps_fingerprint',{}).get('selected_objects',{}) and r['exit_status']==0]
assert audits
final=audits[-1];out=(P/final['attempt']/'stdout.log').read_text();start=out.index('theorem AspisR1.Rc10_Top.deployed');kernel=out[start:].split("'AspisR1.Rc10_Top.deployed' depends on axioms:")[0].rstrip()+'\n';(P/'JFm_AFTER_Rc10_KERNEL.txt').write_text(kernel)
old=json.loads((R/'evidence/joint-fixture10-20261026/JFp_LEDGER_DELTA.json').read_text())['after_object'];new=final['deps_fingerprint']['selected_objects']['Rc10_Top.olean'];assert old['sha256']==new['sha256']
counts=dict(T=89,P=16,G=13,C=0);zero=dict(T=0,P=0,G=0,C=0)
ledger=dict(target='AspisR1.Rc10_Top.deployed',method='design/PREMISE-LEDGER-20261025.md: Rc10 quantified atomic-law families, conjunction leaves, guarded conditional laws and common witnesses, with deployment rows; L185 aliases L159; native/global copies remain distinct',before=counts,after=counts,actual_distinct=dict(T=83,P=12,G=13,C=0),deployment_non_alias=dict(T=6,P=4,G=0,C=0),removed=zero,added=zero,changed=zero,before_source_sha256=sha(before),after_source_sha256=sha(source),source_statements_identical=True,before_object=old,after_object=new,target_object_hash_unchanged=True,limitations='No complete accepted native pair or actual-top premise removal. Partial real-byte source fixture does not imply acceptance or source/syscall/artifact refinement. No quantifier, carrier, failure event, numerical constant, game clause or trust item changed.')
(P/'JFm_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
summary=dict(charged=len(rows),lean_processes=len(rows),passes=sum(r['exit_status']==0 for r in rows),rejects=sum(r['exit_status']!=0 for r in rows),kani=0,modules=len(valid),wall_seconds=sum(r['wall_seconds'] for r in rows),max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),final=rows[-1],source_statements_identical=True,target_object_hash_unchanged=True)
(P/'JFm_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k!='final'})
