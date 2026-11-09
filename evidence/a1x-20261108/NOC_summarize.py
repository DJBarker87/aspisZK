from pathlib import Path
import json,csv,hashlib
E=Path(__file__).resolve().parent
rows=[];roots=[]
for p in sorted(E.glob('NOC_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());r['receipt']=str(p.relative_to(E));rows.append(r)
 if r['exit_status']==0:roots.append(dict(module=r['module'],attempt=r['attempt'],axioms=r.get('print_axioms',[])))
with (E/'NOC_COMPILE.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['attempt','module','exit','wall_s','peak_RSS_KiB','swap','revision','source_hashes','dependency_fingerprint_sha256','axioms','receipt'])
 for r in rows:w.writerow([r['attempt'],r['module'],r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'],r['source_revision'],json.dumps(r.get('source_hashes',{})),hashlib.sha256(json.dumps(r.get('deps_fingerprint',{}),sort_keys=True).encode()).hexdigest(),json.dumps(r.get('print_axioms',[])),r['receipt']])
(E/'NOC_ACCEPTED_ROOTS.json').write_text(json.dumps(roots,indent=2)+'\n')
with (E/'NOC_TRANSCRIPT_SUMMARIES.jsonl').open('w') as f:
 for r in rows:
  out=(E/r['attempt']/'stdout.log').read_text()
  errors=[l for l in out.splitlines() if ': error' in l]
  f.write(json.dumps(dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'],wall_s=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swap=r['swaps'],summary=errors[0] if errors else 'Accepted focused import/proof; standard printed axioms',receipt=r['receipt']))+'\n')
print(json.dumps(dict(scopes=len(rows),passes=sum(r['exit_status']==0 for r in rows),failures=sum(r['exit_status']!=0 for r in rows))))
