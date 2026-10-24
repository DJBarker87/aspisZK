#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,tarfile
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021/s6-sdk-first-20261024';E.mkdir(exist_ok=True)
cache=Path('/tmp/s126-s6-sdk-first-20261024-cache');cache.mkdir(exist_ok=True)
roots=[Path('/tmp/s126-current-caller-20261021-objects')]+[Path(p) for p in Path('/tmp/s126-round-trace-path-20261024.txt').read_text().strip().split(':')]
# Existing selected S6/S1 cached closure, plus any other available top-level project module.
known=set();local={}
for root in roots:
 if not root.is_dir():continue
 for p in root.glob('*.olean'):
  if p.is_file() and p.stem not in local:known.add(p.stem);local[p.stem]=str(p)
# Include the complete existing transitive-module name inventory.
j=json.loads((B/'evidence/s126-current-caller-20261021/s1-accepted-rounds-numeric-import-pins.json').read_text())
for row in j['modules']:known.add(row['name']);local.setdefault(row['name'],row['path'])
(cache/'known.json').write_text(json.dumps(sorted(known))+'\n');(cache/'local.json').write_text(json.dumps(local)+'\n')
reader=(R/'tools/s126-sdk-20261021/pin-imports.py').read_text().split('\nB=Path',1)[0];(cache/'header-reader.py').write_text(reader)
host='dombarker@100.108.41.90';W='/home/dombarker/project-offloads/s126-real-sdk-20261021/s6-sdk-first-cache-20261024'
subprocess.run(['ssh',host,'mkdir -p '+W],check=True)
for p in [cache/'known.json',cache/'header-reader.py',R/'tools/s6-sdk-first-20261024/cache-host.py']:subprocess.run(['scp','-q',str(p),host+':'+W+'/'+p.name],check=True)
subprocess.run(['ssh',host,'python3 '+W+'/cache-host.py'],check=True)
for n in ['inventory.json','objects.tar.gz','lean-106-receipt.json','lean-109-receipt.json','lean-110-receipt.json']:subprocess.run(['scp','-q',host+':'+W+'/'+n,str(cache/n)],check=True)
with tarfile.open(cache/'objects.tar.gz') as t:t.extractall(cache/'recovered',filter='data')
m=json.loads((cache/'inventory.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for row in m['modules']:
 for f in row['files']:assert sha(cache/'recovered'/f['relative'])==f['sha256']
 if 'source' in row:assert sha(cache/'recovered'/row['source']['relative'])==row['source']['sha256']
for row in m['common']:
 p=Path(local[row['name']]);row['local_object']=str(p);row['local_sha256']=sha(p);row['same_object']=row['sha256']==row['local_sha256']
(E/'reused-cache.json').write_text(json.dumps(m,indent=2)+'\n')
for n in ['lean-106-receipt.json','lean-109-receipt.json','lean-110-receipt.json']:(E/n).write_bytes((cache/n).read_bytes())
Path('/tmp/s126-s6-sdk-first-path-20261024.txt').write_text(str(cache/'recovered')+':'+Path('/tmp/s126-round-trace-path-20261024.txt').read_text().strip()+'\n')
print(json.dumps(dict(recovered=len(m['modules']),common=len(m['common']),different_common=sum(not r['same_object'] for r in m['common']))))
