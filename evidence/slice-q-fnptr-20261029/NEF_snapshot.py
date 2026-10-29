from NEF_host import *
import subprocess,difflib,hashlib
admit('NEF_SNAPSHOT001')
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})/'NEF_src';out={{}}
for p in b.rglob('*'):
 if p.is_file() and p.suffix in ['.rs','.toml','.lock','.lean']:
  data=p.read_bytes();out[str(p.relative_to(b))]=dict(git_blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest(),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
actual=json.loads(r.stdout)
frozen={}
for line in subprocess.check_output(['git','ls-tree','-r','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'],text=True).splitlines():
 meta,name=line.split('\t');frozen[name]=meta.split()[2]
changed=[n for n,v in actual.items() if v['git_blob']!=frozen.get(n)]
r=py(f'''from pathlib import Path
import json
b=Path({B!r})/'NEF_src';names={changed!r};print(json.dumps({{n:(b/n).read_text() for n in names}}))
''');assert r.returncode==0,r.stderr
patch=[]
for n,t in json.loads(r.stdout).items():
 old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True,stderr=subprocess.DEVNULL) if n in frozen else ''
 patch+=difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n if n in frozen else '/dev/null',tofile='b/'+n)
(E/'NEF_SCRATCH_FINAL.patch').write_text(''.join(patch))
(E/'NEF_SCRATCH_FINAL_PINS.json').write_text(json.dumps(dict(files=actual,changed_paths=changed,frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',patch_sha256=hashlib.sha256(''.join(patch).encode()).hexdigest()),indent=2)+'\n')
print(json.dumps(dict(files=len(actual),changed=changed)))
