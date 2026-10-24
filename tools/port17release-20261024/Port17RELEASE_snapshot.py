#!/usr/bin/env python3
"""Snapshot only A's immutable-pinned warm objects missing/different on host."""
import json,pathlib,hashlib,tarfile,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];E=ROOT/'evidence/port17release-20261024'
r=json.load(open('/tmp/port17release-host-comparison.json'));rows=[]
with tarfile.open('/tmp/port17release-dependency-objects.tar','w',dereference=True) as tar:
 for m in r['missing']+r['different']:
  p=pathlib.Path(m['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256'],m['name']
  key=m['name'].replace('.','/')+'.olean'
  for suffix in ['', '.server','.private']:
   q=pathlib.Path(str(p)+suffix)
   if q.exists():
    data=q.read_bytes();tar.add(q,arcname=key+suffix,recursive=False)
    rows.append({'module':m['name'],'file':key+suffix,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'source':str(q)})
  q=p.with_suffix('.ir')
  if q.exists():
   data=q.read_bytes();tar.add(q,arcname=key[:-6]+'.ir',recursive=False)
   rows.append({'module':m['name'],'file':key[:-6]+'.ir','sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'source':str(q)})
(E/'dependency-object-snapshot.json').write_text(json.dumps({'immutable_commit':'a4fa5c5ab357a4f6732a3e053965640c90a0df1e','objects':rows,'no_objects_committed':True},indent=2)+'\n')
print('snapshot files',len(rows))
