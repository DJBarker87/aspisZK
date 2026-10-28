from NCJ_host import *
import difflib,sys
name=sys.argv[1]
paths=['crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/NCJ_weights.rs','KMX_stubs.rs']
r=py(f'''from pathlib import Path
import json
s=Path({(B+'/NCJ_src')!r});print(json.dumps({{n:(s/n).read_text() for n in {paths!r}}}))
''');assert r.returncode==0,r.stderr
snap=json.loads(r.stdout);patch=''
for p,s in snap.items():
 r=subprocess.run(['git','show','4bb3b3f5:'+p],capture_output=True,text=True)
 before=r.stdout if r.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(before.splitlines(True),s.splitlines(True),fromfile='a/'+p if before else '/dev/null',tofile='b/'+p))
p=E/(name+'.patch');assert not p.exists();p.write_text(patch)
print(p,hashlib.sha256(patch.encode()).hexdigest())
