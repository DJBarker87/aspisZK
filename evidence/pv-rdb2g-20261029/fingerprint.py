"""Freeze exact source, dependency and byte-hash comparisons; never compile."""
from pathlib import Path
import json,hashlib,lzma
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2g-20261029');p=json.loads((D/'plan.json').read_text());env=json.loads((D/'env-J.json').read_text());assert env==p['environment'];O=Path(env['LEAN_PATH'].split(':')[0]);roots=list(map(Path,env['LEAN_PATH'].split(':')));F=D.with_name('codex-pv-rdb2f-20261029')
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def obj(m):return next((root/(m.replace('.','/')+'.olean') for root in roots if(root/(m.replace('.','/')+'.olean')).exists()),None)
rows=[];diffs=[]
for r in p['objects']:
 m=r['module'];s=F/'lean-sources'/(m.replace('.','/')+'.lean');assert sha(s)==r['source']['sha256'];q=obj(m)
 # Required rebuilds must exist in the original private prefix: never fall through to a stale external object.
 if m in p['build_order'] and not (O/(m.replace('.','/')+'.olean')).exists():q=None
 row=dict(module=m,source=r['source'],path=str(q) if q else None,rebuilt=m in p['build_order'],previous_sha256=r['object_sha256'])
 if q:
  h=sha(q);row.update(sha256=h,bytes=q.stat().st_size,matches_rdb2f=h==r['object_sha256'],imports=[])
  if h!=r['object_sha256']:diffs.append(dict(module=m,previous=r['object_sha256'],actual=h))
  for i in r['imports']:
   dep=obj(i['module']);expected=i.get('sha256',i.get('object_sha256'));actual=sha(dep) if dep else None
   row['imports'].append(dict(module=i['module'],path=str(dep),expected=expected,actual=actual,matches=actual==expected))
  row['companions']=[dict(path=str(c),sha256=sha(c),bytes=c.stat().st_size) for c in [q.with_suffix('.ir'),Path(str(q)+'.server'),Path(str(q)+'.private')] if c.exists()]
 rows.append(row)
external=[]
for r in p['external']:
 q=obj(r['module']);h=sha(q);assert h==r['actual'];external.append(dict(module=r['module'],path=str(q),sha256=h))
j=dict(environment=env,effective_LEAN_PATH=str(O)+':'+env['LEAN_PATH'],objects=rows,external=external,object_differences=diffs,missing_rebuilds=[r['module'] for r in rows if r['rebuilt'] and r['path'] is None],all_178_source_files_unchanged=True,all_5673_external_hashes_unchanged=True)
raw=json.dumps(j,indent=2).encode();(D/'fingerprint.json.xz').write_bytes(lzma.compress(raw,preset=6));(D/'fingerprint.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');summary=dict(rebuilt=sum(r['rebuilt'] and r['path'] is not None for r in rows),unchanged_cached=sum(not r['rebuilt'] for r in rows),object_differences=diffs,missing_rebuilds=j['missing_rebuilds'],rebuilt_dependency_mismatches=[dict(module=r['module'],dependency=i) for r in rows if r['rebuilt'] and r.get('path') for i in r['imports'] if not i['matches']]);(D/'comparison.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary))
