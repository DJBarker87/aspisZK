"""Remove only this round's completed query-only compiled artifacts and links."""
import json
from pathlib import Path
from RPz8_attempt import E,R,B,ssh,collect
plans=[json.loads((E/f).read_text()) for f in ['RPz8_plan.json','RPz8_ARX-plan.json']];source_modules={r['module'] for p in plans for r in p['rows']};artifacts=[]
for line in (E/'RPz8_overlay-additions.jsonl').read_text().splitlines():
 d=json.loads(line)
 if d['module'] in source_modules:continue
 for link,x in d['artifacts'].items():artifacts.append({'link':link,'path':x['target'],'sha256':x['sha256'],'bytes':x['bytes'],'module':d['module']})
payload='''from pathlib import Path
import json,hashlib
B=Path(%r);rows=json.loads(%r);removed=[]
for x in rows:
 p=Path(x['path']);link=Path(x['link'])
 assert p.parent==B/'RPz8_objects' and p.name.startswith('RPz8_'),p
 assert link.parent==B/'RPz8_overlay' and link.is_symlink() and link.resolve()==p,link
 assert p.is_file() and not p.is_symlink() and hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256'] and p.stat().st_size==x['bytes'],p
 link.unlink();p.unlink();removed.append(x)
out={'removed_query_only_objects':removed,'accepted_source_cache_retained':True,'qualification':'Performed after final verification; only this job query outputs are removed, never accepted source proofs or keys.'}
(B/'RPz8_cleanup.json').write_text(json.dumps(out,indent=2)+'\\n');print(json.dumps({'removed':len(removed)}))
'''%(B,json.dumps(artifacts))
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr;collect('RPz8_cleanup.json');print(r.stdout)
