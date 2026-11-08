from pathlib import Path
import json,csv,hashlib
E=Path(__file__).resolve().parent
rows=[]
for p in sorted(E.glob('NNV_L[0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());rows.append([r['attempt'],r['module'],r['exit_status'],r['wall_seconds'],r['peak_rss_kib'],r['swaps'],r['source_revision'],json.dumps(r['source_hashes'],sort_keys=True),hashlib.sha256(json.dumps(r['deps_fingerprint'],sort_keys=True).encode()).hexdigest(),json.dumps(r['command']),json.dumps(r['print_axioms'])])
with (E/'NNV_COMPILE.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['attempt','target','exit','wall_seconds','peak_rss_kib','swap','revision','source_sha256','dependencies_sha256','command','print_axioms']);w.writerows(rows)
print(f'{len(rows)}/100 scopes; '+str(sum(r[2]==0 for r in rows))+' passes')
