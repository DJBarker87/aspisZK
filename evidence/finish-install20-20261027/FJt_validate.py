"""Validate task receipts, current source coverage and standard-axiom audits."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent;R=E.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for p in sorted(E.glob('FJt_*/receipt.json')):
 x=json.loads(p.read_text());x['receipt_path']=str(p.relative_to(R));receipts.append(x)
assert len(receipts)==59
allowed={'propext','Classical.choice','Quot.sound'}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for x in receipts:
 assert x['limits']==limits,x['attempt']
 assert x['command'][1:]==['env','lean','-j1','-M7000','-DElab.async=false','-o',x['sources'][0].replace('.lean','.olean'),x['sources'][0]]
 assert x['swaps']=='0'
 assert int(x['peak_rss_kib'])<8*1024*1024
 if x['exit_status']==0:
  for line in x['print_axioms']:
   ax=re.search(r'\[(.*)\]',line)
   if ax:assert set(re.sub(r'\.\{[^}]*\}','',ax.group(1)).split(', '))<=allowed,(x['attempt'],line)
current={}
for p in sorted((R/'lean').glob('FJt_*.lean')):
 h=sha(p);hits=[x['attempt'] for x in receipts if x['exit_status']==0 and x['source_hashes'].get(p.name)==h]
 assert hits,p
 current[p.name]={'sha256':h,'passing_attempts':hits}
 # No admissions or resource/heartbeats changes in any delivered Lean module.
 assert not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
names=json.loads((E/'FJt_THEOREMS.json').read_text())
audit=(E/'FJt_059/stdout.log').read_text()
for n in names:assert "'"+n+"' depends on axioms:" in audit,n
assert 'sorryAx' not in audit and 'error:' not in audit
failures=[dict(attempt=x['attempt'],target=x['sources'][0],exit_status=x['exit_status']) for x in receipts if x['exit_status']!=0]
result=dict(charged_lean_attempts=60,compiler_starts=len(receipts),passing_compiler_runs=sum(x['exit_status']==0 for x in receipts),failures=failures,preflight_failure='FJt_016: missing unchanged IDa_Deployed object; rebuilt017',kani_runs=0,limits=limits,max_peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),all_swaps_zero=True,delivered_sources=current,delivered_theorem_roots=len(names),combined_axiom_audit='FJt_059',statements_audit='FJt_060',source_revisions=sorted(set(x['source_revision'] for x in receipts)),package_replays=0,wall_timeouts=0,memory_kills=0)
(E/'FJt_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
with (E/'FJt_ATTEMPTS.jsonl').open('w') as f:
 for x in receipts:f.write(json.dumps(x,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['delivered_sources','source_revisions']},indent=2))
