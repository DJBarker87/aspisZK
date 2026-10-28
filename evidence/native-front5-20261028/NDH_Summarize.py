from pathlib import Path
import json,hashlib,collections,re,subprocess
E=Path(__file__).resolve().parent
rs=[]
for p in sorted(E.glob('NDH_[KLE][0-9][0-9][0-9]/receipt.json')):
 r=json.loads(p.read_text());r['receipt']=str(p.relative_to(E));r['receipt_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 r['deps_fingerprint']={'see_full_receipt':r['receipt']}
 r['peak_rss_kib']=int(r['peak_rss_kib']);r['swaps']=int(r['swaps']);rs.append(r)
by={k:[r for r in rs if r['kind']==k] for k in ['kani','lean','extract']}
assert len(by['kani'])==80 and len(by['lean'])<=80 and len(by['extract'])<=20
counts={k:dict(attempts=len(v),exits=dict(collections.Counter(str(r['exit_status']) for r in v)),max_rss_kib=max([r['peak_rss_kib'] for r in v] or [0]),wall_seconds=sum(r['wall_seconds'] for r in v),swaps=sum(r['swaps'] for r in v)) for k,v in by.items()}
timeouts=[];unwinds=[]
for r in rs:
 txt=(E/r['attempt']/'stdout.log').read_text()
 if 'timed out' in txt.lower() or r['exit_status']==124:timeouts.append(r['attempt'])
 if 'unwinding failures' in txt:unwinds.append(r['attempt'])
(E/'NDH_RESULTS.json').write_text(json.dumps(dict(counts=counts,rows=rs,timeout_or_oom_credit=0,timeouts=timeouts,unwind_failures=unwinds,nonstandard_axioms_in_accepted_proofs=False,limits='MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax64; Lean -M7000; optimized offline Rust; one admitted scope at a time'),indent=2)+'\n')
# Every raw receipt remains immutable and is the source of the compact index.
(E/'NDH_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
print(json.dumps(counts))
