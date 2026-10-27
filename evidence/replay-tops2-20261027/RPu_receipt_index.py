from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
rs=sorted([json.loads(f.read_text()) for f in E.glob('RPu_*/receipt.json')],key=lambda d:int(d['attempt'].split('_')[1]))
with (E/'RPu_attempts.jsonl').open('w') as out:
 for d in rs:
  row={k:d[k] for k in ['attempt','module','command','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms','reservation_retries']}
  row['receipt']=d['attempt']+'/receipt.json';row['full_output']=d['attempt']+'/stdout.log';row['deps_fingerprint_sha256']=hashlib.sha256(json.dumps(d['deps_fingerprint'],sort_keys=True).encode()).hexdigest();row['receipt_sha256']=hashlib.sha256((E/row['receipt']).read_bytes()).hexdigest();row['output_sha256']=hashlib.sha256((E/row['full_output']).read_bytes()).hexdigest()
  out.write(json.dumps(row)+'\n')
print('indexed',len(rs),'attempts')
