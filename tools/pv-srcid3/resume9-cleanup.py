#!/usr/bin/env python3
"""Remove only this allocation's verified private compiled caches, retaining evidence."""
import pathlib,json,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
r=[json.loads(l) for l in (e/'resume9-attempts.jsonl').read_text().splitlines()];accepted={q['module']:q for q in r if q['accepted']}
code='''import pathlib,hashlib,json
job=pathlib.Path('/home/dombarker/project-offloads/codex-pv-srcid-20261026');joint=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects');cache=job/'lean-objects';expected=EXPECTED;rows=[]
for mod,sha in expected.items():
 p=cache/(mod+'.olean');q=joint/(mod+'.olean')
 assert p.is_file() and q.is_file(),mod
 hp=hashlib.sha256(p.read_bytes()).hexdigest();hq=hashlib.sha256(q.read_bytes()).hexdigest()
 assert hp==hq==sha,(mod,hp,hq,sha)
 rows.append(dict(path=str(p),sha256=sha,bytes=p.stat().st_size,shared_object_sha256=hq,removed=False))
for row in rows:pathlib.Path(row['path']).unlink();row['removed']=True
for d in sorted(cache.rglob('*'),key=lambda p:len(p.parts),reverse=True):
 if d.is_dir() and not any(d.iterdir()):d.rmdir()
if cache.is_dir() and not any(cache.iterdir()):cache.rmdir()
print(json.dumps(dict(rows=rows,files=len(rows),bytes=sum(r['bytes'] for r in rows),shared_objects_retained=True,sources_and_evidence_retained=True,wallet_or_account_keys_created_or_touched=False,remaining_private_cache_files=[str(p) for p in cache.rglob('*') if p.is_file()] if cache.exists() else [])))
'''.replace('EXPECTED',repr({m:q['object_sha256'] for m,q in accepted.items()}))
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,capture_output=True,text=True,check=True)
result=json.loads(p.stdout);(e/'resume9-cache-cleanup.json').write_text(json.dumps(result,indent=2)+'\n');print('Removed verified private cache',result['files'],'objects,',result['bytes'],'bytes; shared objects/evidence retained')
