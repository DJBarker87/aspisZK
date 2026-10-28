from pathlib import Path
import subprocess,tarfile,io,json
E=Path('evidence/pv-batch2-20261027/batch2f');D='/home/dombarker/project-offloads/codex-pv-batch2-20261027'
code='''from pathlib import Path
import tarfile,sys
D=Path(DIR)
with tarfile.open(fileobj=sys.stdout.buffer,mode='w|') as t:
 for root in (D/'candidate').glob('batch2f-box*'):
  if not root.is_dir():continue
  for p in root.rglob('*'):
   if not p.is_file() or any(x in p.parts for x in ['artifacts','diagnostics']):continue
   if p.suffix in ['.json','.log','.txt']:t.add(p,arcname=str(p.relative_to(D)),recursive=False)
'''.replace('DIR',repr(D))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code.encode(),capture_output=True,check=True)
with tarfile.open(fileobj=io.BytesIO(r.stdout)) as t:t.extractall(E,filter='data')
rows=[]
for p in (E/'candidate').glob('batch2f-box*/comparison.json'):
 j=json.loads(p.read_text());rec=json.loads((p.parent/'receipt/receipt.json').read_text());j.update({k:rec[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']});j['receipt']=str((p.parent/'receipt/receipt.json').relative_to(E));rows.append(j)
(E/'ELF-STAGES.json').write_text(json.dumps(rows,indent=2)+'\n');assert all(r['matches'] and r['exit_status']==0 for r in rows)
print('collected',len(rows),'matching ELF receipts; no keys or binaries copied')
