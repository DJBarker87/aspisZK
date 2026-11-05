"""Content-address source snapshots once; preserve every receipt's exact inputs."""
from pathlib import Path
import json,lzma,hashlib,shutil,sys
E=Path(__file__).resolve().parent;M=E/'NHJ_INPUTS.json';index=json.loads(M.read_text()) if M.exists() else dict(objects={},attempts={})
sha=lambda b:hashlib.sha256(b).hexdigest();check='--check' in sys.argv
for p in sorted(E.glob('NHJ_[KL]???/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];mapping=index['attempts'].setdefault(a,{})
 for n,h in r['source_hashes'].items():
  s=p.parent/'sources'/n
  if s.exists():
   data=s.read_bytes();assert sha(data)==h
   if not check:
    path=E/'NHJ_INPUTS'/(h+'.xz');path.parent.mkdir(exist_ok=True)
    if not path.exists():path.write_bytes(lzma.compress(data,preset=6))
    index['objects'][h]=dict(path=str(path.relative_to(E)),bytes=len(data),archive_sha256=sha(path.read_bytes()))
    mapping[n]=h
  assert mapping.get(n)==h,(a,n,'missing input index')
  obj=index['objects'][h];q=E/obj['path'];assert sha(q.read_bytes())==obj['archive_sha256'];data=lzma.decompress(q.read_bytes());assert sha(data)==h and len(data)==obj['bytes']
 if not check and (p.parent/'sources').is_dir():shutil.rmtree(p.parent/'sources')
if not check:M.write_text(json.dumps(index,indent=1)+'\n')
print(json.dumps(dict(status='PASS',attempts=len(index['attempts']),unique_objects=len(index['objects']),unique_bytes=sum(x['bytes'] for x in index['objects'].values()))))
