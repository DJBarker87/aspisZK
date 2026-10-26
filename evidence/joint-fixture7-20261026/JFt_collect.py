from pathlib import Path
import hashlib,json,re,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[]
for n in range(1,101):
 a=f'JFt_{n:03}';f=P/a/'receipt.json'
 if f.exists():
  r=json.loads(f.read_text());r['receipt']=str(f.relative_to(R))
  r['errors']=[line for line in (P/a/'stdout.log').read_text().splitlines() if 'error:' in line or 'error(' in line]
 else:
  assert n==5
  r=json.loads((P/'JFt_005_FAILURE.json').read_text());cfg=json.loads((P/'JFt_005.json').read_text())
  r.update(source_revision=cfg['source_revision'],source_tree_dirty=cfg['source_tree_dirty'],source_hashes=None,deps_fingerprint='not computed: launcher rejects missing direct import before Lean',command=cfg['command'],limits='requested 6G high / 8G max / swap0 / tasks64; no Lean process',receipt='JFt_005-launch.log')
 rows.append(r)
(P/'JFt_RECORDS_MANIFEST.json').write_text(json.dumps(rows,indent=2)+'\n')
valid={}
for f in sorted((R/'lean').glob('JFt_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest()
 matches=[r for r in rows if r.get('exit_status')==0 and (r.get('source_hashes') or {}).get(f.name)==sha]
 assert matches, f
 r=matches[-1]
 assert all('sorryAx' not in a for a in r['print_axioms'])
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   axioms=line.split('depends on axioms:',1)[1].strip().strip('[]')
   assert set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},line
 valid[f.name]=dict(sha256=sha,attempt=r['attempt'],receipt=r['receipt'],axioms=r['print_axioms'])
(P/'JFt_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
stdout=(P/'JFt_100'/'stdout.log').read_text()
after=stdout.split("'AspisR1.Rc7_Top.deployed' depends on axioms:")[0].rstrip()+'\n'
(P/'JFt_AFTER_Rc7_KERNEL.txt').write_text(after)
ledger=json.loads((P/'JFt_LEDGER_DELTA.json').read_text());ledger['kernel_print_identical']=(P/'JFt_BEFORE_Rc7_KERNEL.txt').read_text()==after
ledger['before_kernel_sha256']=hashlib.sha256((P/'JFt_BEFORE_Rc7_KERNEL.txt').read_bytes()).hexdigest();ledger['after_kernel_sha256']=hashlib.sha256(after.encode()).hexdigest()
(P/'JFt_LEDGER_DELTA.json').write_text(json.dumps(ledger,indent=2)+'\n')
receipts=[r for r in rows if r.get('wall_seconds') is not None]
summary=dict(charged=100,lean_processes=len(receipts),preflight_rejections=1,passes=sum(r['exit_status']==0 for r in receipts),rejects=sum(r['exit_status']!=0 for r in receipts),kani=0,modules=len(valid),wall_seconds=sum(r['wall_seconds'] for r in receipts),max_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),kernel_print_identical=ledger['kernel_print_identical'],final=rows[-1])
(P/'JFt_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print({k:v for k,v in summary.items() if k!='final'})
