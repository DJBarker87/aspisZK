from KMZ_driver import *
refs={};attempts={}
def valid(p,sha):return p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==sha
for rp in sorted(E.glob('KMZ_*/receipt.json')):
 rc=json.loads(rp.read_text());files={}
 for n,sha in rc['source_hashes'].items():
  choices=[E/n,E/'sources'/(sha+'.rs'),E/'sources'/(sha+'.txt'),OLD/n,OLD/'sources'/(sha+'.txt')]
  found=next((p for p in choices if valid(p,sha)),None)
  if found is None:refs.setdefault(sha,(rc['attempt'],n))
  files[n]=dict(sha256=sha,archive=str(found.relative_to(E)) if found and found.is_relative_to(E) else '../'+str(found.relative_to(E.parent)) if found else 'sources/'+sha+'.txt')
 attempts[rc['attempt']]=files
if refs:
 r=t.remote_py('from pathlib import Path\nimport hashlib,json\nb=Path('+repr(t.B)+');refs='+repr(refs)+'\nout={}\nfor sha,(a,n) in refs.items():\n p=b/a/"sources"/n;s=p.read_text();assert hashlib.sha256(s.encode()).hexdigest()==sha,(a,n);out[sha]=s\nprint(json.dumps(out))')
 assert r.returncode==0,r.stderr
 for sha,s in json.loads(r.stdout).items():(E/'sources'/(sha+'.txt')).write_text(s)
for a,files in attempts.items():
 for n,x in files.items():assert valid(E/x['archive'],x['sha256']),(a,n,x)
(E/'KMZ_SOURCE_ARCHIVE.json').write_text(json.dumps(dict(attempts=attempts,baseline='KMY immutable snapshots are referenced, not recopied; all referenced bytes were hash-verified',unique_source_hashes=len({x['sha256'] for fs in attempts.values() for x in fs.values()})),indent=2)+'\n')
print('Indexed',len(attempts),'attempts; recovered',len(refs),'missing source versions')
