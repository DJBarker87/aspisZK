from pathlib import Path
import json,hashlib,tarfile,lzma,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
export=json.loads((B/'NJM_EXPORT.json').read_text())
for r in export['files']:assert sha(Path(r['path']))==r['sha256'],r['path']
resolved=json.loads((B/'NJM_RESOLVED_OBJECTS.json').read_text())
for r in resolved:
 p=Path(r['path'])
 for suffix,size,h in r['parts']:
  q=p if suffix=='' else p.with_suffix('.ir') if suffix=='ir' else Path(str(p)+suffix)
  assert q.stat().st_size==size and sha(q)==h,str(q)
assert any(r['module'].startswith('Aeneas') for r in resolved)
assert sha(B/'NJM_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
paths=json.loads((B/'NJM_CONSUMER_PATHS.json').read_text());assert paths[0]==export['path'] and str(B/'NJM_objects') not in paths
r=json.loads((B/'NJM_L099/receipt.json').read_text());assert r['exit_status']==0 and len(r['print_axioms'])==4
assert all('sorryAx' not in x for x in r['print_axioms'])
result=dict(status='PASS',retained_files=len(export['files']),resolved_modules=len(resolved),aeneas_modules=sum(r['module'].startswith('Aeneas') for r in resolved),frozen_lock_unchanged=True,consumer_receipt='NJM_L099/receipt.json',consumer_search_path=paths,working_objects_in_search_path=False,export_first=True)
(B/'NJM_CONSUMER_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
D=B/'NJM_archives';D.mkdir(exist_ok=True);archives=[]
sets={'NJM_RAW_LOGS':sorted(set([*B.glob('NJM_[LKE][0-9][0-9][0-9]/stdout.log'),*B.glob('NJM_[LKE][0-9][0-9][0-9]/time.log'),*B.glob('NJM_audit/**/*.log'),*B.glob('NJM_audit/**/*.time')])), 'NJM_RAW_REACHABILITY':sorted(B.glob('NEP_*_REACHABLE.txt'))}
for name,files in sets.items():
 assert files,name
 dst=D/(name+'.tar.xz')
 with tarfile.open(dst,'w:xz') as tf:
  for f in files:tf.add(f,arcname=str(f.relative_to(B)),recursive=False)
 digest=hashlib.sha256()
 with lzma.open(dst,'rb') as inp:
  while chunk:=inp.read(1024*1024):digest.update(chunk)
 (D/(name+'.tar.sha256')).write_text(digest.hexdigest()+'  '+name+'.tar\n')
 assert dst.stat().st_size<=20_000_000
 archives.append(dict(path=str(dst.relative_to(B)),sha256=sha(dst),bytes=dst.stat().st_size,uncompressed_tar_sha256=digest.hexdigest(),files=[dict(path=str(f.relative_to(B)),bytes=f.stat().st_size,sha256=sha(f)) for f in files]))
(B/'NJM_RAW_ARCHIVES.json').write_text(json.dumps(archives,indent=2)+'\n')
clean=[]
for name in ['NJM_target','NJM_tmp']:
 p=B/name
 if not p.exists():continue
 files=[q for q in p.rglob('*') if q.is_file()]
 keys=[str(q) for q in files if q.name.endswith(('-keypair.json','.pem','.key'))]
 if keys:clean.append(dict(path=str(p),status='KEPT',reason='possible keys; no cleanup authorized',files=keys));continue
 count=len(files);size=sum(q.stat().st_size for q in files);shutil.rmtree(p);clean.append(dict(path=str(p),status='REMOVED_OWN_REBUILDABLE_OUTPUTS',files=count,bytes=size))
stat=shutil.disk_usage(B)
(B/'NJM_HOST_END.json').write_text(json.dumps(dict(export=export['path'],export_bytes=export['total_bytes'],resolved_modules=len(resolved),cleanup=clean,free_bytes=stat.free,total_bytes=stat.total,cache_deleted=False,keys_touched=False),indent=2)+'\n')
print(json.dumps(dict(export_verified=True,consumer_pass=True,resolved_modules=len(resolved),archives=len(archives),cache_retained=True,free_bytes=stat.free)))
