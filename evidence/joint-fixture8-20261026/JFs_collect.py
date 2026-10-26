"""Collect exact checked receipts and distinguish rejected drafts."""
from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[]
for n in range(1,101):
 a=f'JFs_{n:03}';f=P/a/'receipt.json'
 assert f.exists(),a
 r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R))
 r['errors']=[line for line in (P/a/'stdout.log').read_text().splitlines() if 'error:' in line or 'error(' in line]
 rows.append(r)
(P/'JFs_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={}
for f in sorted((R/'lean').glob('JFs_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest()
 matches=[r for r in rows if r['exit_status']==0 and r.get('source_hashes',{}).get(f.name)==sha]
 assert matches,f
 r=matches[-1]
 for line in r['print_axioms']:
  assert 'sorryAx' not in line,line
  if 'depends on axioms:' in line:
   ax=line.split('depends on axioms:',1)[1].strip().strip('[]')
   assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},line
 valid[f.name]=dict(sha256=sha,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFs_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
source=(R/'lean/Rc8_Top.lean').read_bytes();(P/'JFs_AFTER_Rc8_Top.lean.txt').write_bytes(source)
ledger=json.loads((P/'JFs_LEDGER_DELTA.json').read_text())
before=(P/'JFs_BEFORE_Rc8_Top.lean.txt').read_bytes()
ledger.update(source_statements_identical=before==source,before_source_sha256=hashlib.sha256(before).hexdigest(),after_source_sha256=hashlib.sha256(source).hexdigest())
old=rows[0]['deps_fingerprint']['selected_objects']['Rc8_Top.olean'];new=rows[-1]['deps_fingerprint']['selected_objects']['Rc8_Top.olean']
ledger.update(target_object_hash_unchanged=old['sha256']==new['sha256'],before_object=old,after_object=new)
stdout=(P/'JFs_100/stdout.log').read_text();kernel=stdout[stdout.index('theorem AspisR1.Rc8_Top.deployed'):].split("'AspisR1.Rc8_Top.deployed' depends on axioms:")[0].rstrip()+'\n'
(P/'JFs_AFTER_Rc8_KERNEL.txt').write_text(kernel)
ledger['after_kernel_sha256']=hashlib.sha256(kernel.encode()).hexdigest();ledger['kernel_display_note']='100 rejected unknown pp.maxDepth; its imported roots and printed axioms are retained as diagnostics, not a passing composed audit. Exact full source statements and selected object hashes are unchanged.'
(P/'JFs_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
summary=dict(charged=100,lean_processes=100,passes=sum(r['exit_status']==0 for r in rows),rejects=sum(r['exit_status']!=0 for r in rows),kani=0,modules=len(valid),wall_seconds=sum(r['wall_seconds'] for r in rows),max_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),final=rows[-1],source_statements_identical=ledger['source_statements_identical'],target_object_hash_unchanged=ledger['target_object_hash_unchanged'])
(P/'JFs_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k!='final'})
