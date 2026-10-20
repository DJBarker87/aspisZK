"""Classify unattempted modules after the source quota stops the driver."""
from pathlib import Path
import json,datetime
D=Path(__file__).resolve().parent
assert (D/'compile-budget-stop.json').exists()
rows=[json.loads(l) for l in (D/'status.jsonl').read_text().splitlines()];by={r['module']:r for r in rows}
man=json.loads((D/'manifest-S.json').read_text());mods={e['module'] for e in man['order']};missing={p[1] for p in man['problems'] if p[0]=='unresolved'}
for e in man['order']:
 m=e['module']
 if m in by:continue
 bad=[x for x in e['imports'] if x in missing or x in mods and not by.get(x,{}).get('status','').startswith('current')]
 r={'module':m,'status':'skipped','reason':'blocked imports' if bad else 'source attempt quota exhausted; remaining assigned attempts reserved for mandatory closure audit','source_revision':man['repo_revision'],'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if bad:r['blocked_imports']=bad
 by[m]=r;rows.append(r)
(D/'status.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
start=datetime.datetime.fromisoformat(rows[0]['timestamp_utc']).timestamp()
end=(D/'compile-budget-stop.json').stat().st_mtime
(D/'driver-wall.json').write_text(json.dumps({'wall_seconds':end-start,'finished_utc':datetime.datetime.fromtimestamp(end,datetime.timezone.utc).isoformat(),'completion':'stopped at source quota; no Lean launched for next_unclaimed_attempt'},indent=2)+'\n')
print('All manifest sources classified:',len(rows))
