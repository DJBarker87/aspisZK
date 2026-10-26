"""Verify final receipts and summarize only recorded compiler evidence."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];receipts=[]
for i in range(1,41):
 a=f'DFm_{i:03d}';r=json.loads((E/a/'receipt.json').read_text());assert r['attempt']==a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['command'][3:6]==['-j1','-M7000','-DElab.async=false']
 for p,h in r['source_hashes'].items():assert hashlib.sha256((E/p).read_bytes()).hexdigest()==h,(a,p)
 assert int(r['swaps'])==0
 assert r['exit_status']==(1 if i in [1,4] else 0),(a,r['exit_status'])
 log=(E/a/'stdout.log').read_text();matches=re.findall(r"'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log)
 r['full_print_axioms']=[dict(name=n,axioms=[x.strip() for x in axs.split(',') if x.strip()]) for n,axs in matches]
 r['errors']=[l for l in log.splitlines() if 'error' in l.lower()]
 receipts.append(r)
summary=dict(status='Evidence-only candidate; not adopted; L188 remains open pending complete release audit',lean_attempts=len(receipts),passed=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),kani_runs=0,wall_seconds_sum=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),timeouts_or_memory_kills=[],full_print_axioms_count=sum(len(r['full_print_axioms']) for r in receipts),attempts=[{k:r[k] for k in ['attempt','module','mode','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','limits','full_print_axioms','errors']} for r in receipts])
(E/'DFm_compile-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
assert json.loads((E/'DFm_parser-semantic-comparison.json').read_text())['all_retained_equal']
assert json.loads((E/'DFm_importers-semantic-comparison.json').read_text())['all_retained_equal']
changed=subprocess.check_output(['git','diff','--name-only','d5781cc0147226895c397a9a2102b49c4552ca63'],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/debug-fmt-20261026/') for p in changed),changed
print(json.dumps({k:v for k,v in summary.items() if k!='attempts'},indent=2))
