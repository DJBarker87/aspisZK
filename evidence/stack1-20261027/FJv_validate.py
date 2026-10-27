from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[]
for f in sorted(E.glob('FJv_*/receipt.json')):
 x=json.loads(f.read_text());receipts.append(x)
 assert x['command'][-4]=='-DElab.async=false' or '-DElab.async=false' in x['command']
 assert '-M7000' in x['command']
 assert str(x['swaps'])=='0'
 assert 'source_revision' in x and 'source_hashes' in x and 'deps_fingerprint' in x and 'cgroup' in x
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for src,h in x['source_hashes'].items():assert sha(f.parent/'sources'/src)==h
 if x['exit_status']==0:
  for line in x['print_axioms']:
   assert 'sorryAx' not in line
   if 'depends on axioms:' in line:
    names=re.sub(r'\.\{[^}]*\}', '', re.search(r'\[(.*)\]',line).group(1)).split(', ')
    assert set(names)<=set(['propext','Classical.choice','Quot.sound'])
current=[]
for p in sorted((R/'lean').glob('FJv_*.lean')):
 matches=[x for x in receipts if x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p)]
 assert matches, f'No current-source pass: {p.name}'
 current.append(dict(module=p.stem,source_sha256=sha(p),passing_attempts=[x['attempt'] for x in matches]))
for p in (R/'lean').glob('FJv_*.lean'):
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text())
preflights=list(E.glob('FJv_*-preflight.json'));used=len(receipts)+len(preflights);assert used<=60
out=dict(charged_attempts=used,compiler_starts=len(receipts),passed=sum(x['exit_status']==0 for x in receipts),failed=sum(x['exit_status']!=0 for x in receipts),preflight_failures=len(preflights),Kani_runs=0,current_sources=current,max_peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=0,scope_policy='one at a time; original 6G/8G/swap0/tasks64; no cap/heartbeat/depth increase',qualification='Focused cached composition plus 15 explicitly recorded unchanged-object restores, not a package or fresh release replay')
(E/'FJv_validation.json').write_text(json.dumps(out,indent=2)+'\n')
(E/'FJv_attempts.json').write_text(json.dumps([dict(attempt=x['attempt'],target=x['sources'],exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],source_hashes=x['source_hashes'],print_axioms=x['print_axioms']) for x in receipts],indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='current_sources'},indent=2))
