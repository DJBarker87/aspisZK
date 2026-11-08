from pathlib import Path
import json,csv,hashlib
E=Path(__file__).resolve().parent
rows=[];roots=[]
for p in sorted(E.glob('NNX_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());r['receipt']=str(p.relative_to(E));rows.append(r)
 if r['exit_status']==0:roots.append(dict(module=r['module'],attempt=r['attempt'],axioms=r.get('print_axioms',[])))
with (E/'NNX_COMPILE.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['attempt','module','exit','wall_s','peak_RSS_KiB','swap','revision','source_hashes','dependency_fingerprint_sha256','axioms','receipt'])
 for r in rows:w.writerow([r['attempt'],r['module'],r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'],r['source_revision'],json.dumps(r.get('source_hashes',{})),hashlib.sha256(json.dumps(r.get('deps_fingerprint',{}),sort_keys=True).encode()).hexdigest(),json.dumps(r.get('print_axioms',[])),r['receipt']])
(E/'NNX_ACCEPTED_ROOTS.json').write_text(json.dumps(roots,indent=2)+'\n')
print(json.dumps(dict(scopes=len(rows),passes=sum(r['exit_status']==0 for r in rows),failures=sum(r['exit_status']!=0 for r in rows))))
