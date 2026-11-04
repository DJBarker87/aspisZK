"""Resolve every scratch hash-gate input to committed bytes, without copying corpora."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
head=subprocess.check_output(['git','rev-parse',head],text=True).strip()
pins=json.loads((E/'NFM_NATIVE_SOURCE_IMPORTS.json').read_text())['files']
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def digest(spec):
 proc.stdin.write((spec+'\n').encode());proc.stdin.flush();header=proc.stdout.readline()
 if header.endswith(b' missing\n'):return None
 oid,kind,size=header.split();assert kind==b'blob';left=int(size);h=hashlib.sha256()
 while left:
  data=proc.stdout.read(min(left,1024*1024));assert data;h.update(data);left-=len(data)
 assert proc.stdout.read(1)==b'\n'
 return dict(git_object=oid.decode(),sha256=h.hexdigest(),bytes=int(size))
out=[];missing=[]
for path,h in sorted(pins.items()):
 found=None
 for rev in ['4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',head]:
  result=digest(rev+':'+path)
  if result and result['sha256']==h:found=dict(path=path,revision=rev,**result);break
 if found:out.append(found)
 else:missing.append(dict(path=path,sha256=h))
proc.stdin.close();proc.wait();assert proc.returncode==0
(E/'NFM_COMMITTED_INPUTS.json').write_text(json.dumps(dict(committed=out,missing=missing),separators=(',',':')))
print('committed',len(out),'unmatched',len(missing),flush=True)
