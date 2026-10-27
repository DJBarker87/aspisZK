from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(f.read_text()) for f in sorted(P.glob('JHh31_*/receipt.json'))]
(P/'JHh_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in rows))
passed=[r for r in rows if r['exit_status']==0];failed=[r for r in rows if r['exit_status']!=0]
for r in passed:
 for a in r['print_axioms']:
  if 'depends on axioms' in a:
   assert set(re.findall(r'\[([^\]]*)\]',a)[-1].replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound',''},(r['attempt'],a)
valid={(name,h):r['attempt'] for r in passed for name,h in r['source_hashes'].items()}
manifest=[]
for f in sorted((R/'lean').glob('JHh_*.lean')):
 h=sha(f.read_bytes());manifest.append(dict(module=f.stem,source_sha256=h,bytes=f.stat().st_size,passing_attempt=valid.get((f.name,h)),status='checked' if (f.name,h) in valid else 'UNCHECKED'))
(P/'JHh_SOURCES.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary=dict(lean_processes=len(rows),lean_budget=100,kani_runs=0,kani_budget=10,passed=len(passed),failed=len(failed),wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'] or 0) for r in rows),swaps=sum(int(r['swaps'] or 0) for r in rows),failures=[dict(attempt=r['attempt'],exit_status=r['exit_status'],module=r['sources']) for r in failed],checked_current_sources=sum(x['status']=='checked' for x in manifest),unchecked_current_sources=[x['module'] for x in manifest if x['status']!='checked'],standard_axioms_only_in_passes=True)
(P/'JHh_VALIDATION.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
