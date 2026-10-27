from pathlib import Path
import hashlib,json,time,re,resource
B=Path('/home/dombarker/project-offloads');T=B/'aspis-fs-generic-20261006/evidence';J=B/'aspis-joint-20261019';U=B/'codex-cx-import-union-20261022';start=time.monotonic();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((T/'EJR_all-restored-sources.json').read_text());bad_source=[r['host_path'] for r in rows if not Path(r['host_path']).is_file() or sha(Path(r['host_path']))!=r['source_sha256']]
for r in json.loads((T/'EJR_library-source-provenance.json').read_text()):
 p=U/'sources'/(r['module']+'.lean')
 if sha(p)!=r['source_sha256']:bad_source.append(str(p))
rs=[json.loads(l) for l in (T/'EJR_attempts.jsonl').read_text().splitlines()]
for r in rs:
 r['lean_exit']=int(re.search(r'Exit status:\s*(\d+)',r['time_log'])[1]);r['validation_exit']=r['exit']
(T/'EJR_attempts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rs))
latest={r['key']:r for r in rs};bad_objects=[];checked=0
for r in latest.values():
 if r['exit']:continue
 root=U/'retained-objects' if r['workspace']=='library' else (J if r['workspace']=='joint' else U)/'objects'
 p=root/(r['module']+'.olean');checked+=1
 if not p.is_file() or sha(p)!=r['object_sha256']:bad_objects.append(str(p))
reuses=[json.loads(l) for l in (T/'EJR_reuses.jsonl').read_text().splitlines()]
for r in reuses:
 p=Path(r['target']);checked+=1
 if not p.is_file() or sha(p)!=r['object_sha256']:bad_objects.append(str(p))
staged=json.loads((T/'EJR-library-staged.json').read_text());bad_library=[]
for r in staged['verified']:
 p=U/'retained-objects'/(r['module'].replace('.','/')+'.olean')
 if not p.is_file() or sha(p)!=r['sha256']:bad_library.append(str(p))
usage=resource.getrusage(resource.RUSAGE_SELF);record=dict(target='restored source bytes and successful/reused object hashes',source_revision=(T/'EJR_revision.txt').read_text().strip(),sources_checked=len(rows)+2,objects_checked=checked,unchanged_library_objects_checked=len(staged['verified']),source_mismatches=bad_source,object_mismatches=bad_objects,library_mismatches=bad_library,exit=0 if not bad_source+bad_objects+bad_library else 1,wall_seconds=time.monotonic()-start,peak_rss_kib=usage.ru_maxrss,swaps=usage.ru_nswap,print_axioms='N/A: read-only artifact validation; proof audits in per-module receipts')
(T/'EJR-final-artifact-check.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record));assert record['exit']==0
