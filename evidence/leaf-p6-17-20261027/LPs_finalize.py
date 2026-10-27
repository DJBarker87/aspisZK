from pathlib import Path
import json,hashlib,subprocess,shlex,time
E=Path(__file__).resolve().parent
host='dombarker@100.108.41.90'
code='''from pathlib import Path
import hashlib,json
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
names=set()
for r in roots:
 for p in ([r/'Aeneas.olean']+list((r/'Aeneas').rglob('*.olean'))):
  if p.is_file():names.add(str(p.relative_to(r)))
selected={n:next(r/n for r in roots if (r/n).is_file()) for n in names}
print(json.dumps(dict(cache={str(p):pin(p) for p in cache.rglob('*') if p.is_file()},aeneas={str(p):pin(p) for p in selected.values()})))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',host,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 with (E/'LPs_FINAL_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode==0:break
 if r.returncode!=255 or retry==10:raise SystemExit(r.stderr)
 time.sleep(60)
remote=json.loads(r.stdout)
(E/'LPs_CACHE_END.json').write_text(json.dumps(remote['cache'],indent=2)+'\n')
(E/'LPs_RESOLVED_LIBRARY_END.json').write_text(json.dumps(remote['aeneas'],indent=2)+'\n')
restored=json.loads((E/'LPs_CACHE_RESTORED.json').read_text())
assert all(remote['cache'][p]==v for p,v in restored.items()),'restored object changed'
assert remote['aeneas']==json.loads((E/'LPs_LIBRARY_PIN.json').read_text()),'resolved library differs'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LPs_L*/receipt.json'))]
assert len(receipts)<=140
accepted={}
for r in receipts:
 if r['exit_status']==0:accepted[r['module']]=r
checks={}
for p in sorted(Path('lean').glob('LPs_*.lean')):
 r=accepted[p.stem]
 source=next(iter(r['source_hashes'].values()))
 assert hashlib.sha256(p.read_bytes()).hexdigest()==source,p
 assert all('sorryAx' not in x for x in r['print_axioms'])
 checks[str(p)]=dict(attempt=r['attempt'],sha256=source,axioms=r['print_axioms'])
assert len(checks)==9
bad=[dict(attempt=r['attempt'],exit=r['exit_status']) for r in receipts if r['exit_status']]
summary=dict(lean_attempts=len(receipts),lean_passed=len(receipts)-len(bad),kani_runs=0,rejected=bad,accepted_sources=checks,wall_seconds=sum(r['wall_seconds'] for r in receipts),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),persistent_cache_retained=True,restored_objects_unchanged=True,resolved_aeneas_pin_unchanged=True,coimport_join='OPEN: L098 duplicate owner',full_manifest_replay=False)
(E/'LPs_FINAL_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['accepted_sources','rejected']}))
