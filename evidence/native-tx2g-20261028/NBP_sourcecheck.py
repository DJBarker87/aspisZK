from pathlib import Path
import subprocess,tarfile,io,json,hashlib,shlex,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2g-20261028'
m=json.loads((E/'NBP_SCRATCH_MANIFEST.json').read_text());arc=subprocess.check_output(['git','archive','4bb3b3f5',*m])
with tarfile.open(fileobj=io.BytesIO(arc)) as t: sizes={f.name:f.size for f in t.getmembers() if f.isfile()}
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NBP_src';m={m!r};sizes={sizes!r}
allowed={{'programs/r1-cost-probe/src/lib.rs':b'\\n#[cfg(kani)]\\nmod NBP_error;\\n','crates/aspis-statement/src/pool_v1/payment_relation.rs':b'\\n#[cfg(kani)]\\nmod NBP_codecs;\\n'}}
errors=[];mods=[]
for name,h in m.items():
 data=(s/name).read_bytes();z=sizes[name]
 if hashlib.sha256(data[:z]).hexdigest()!=h:errors.append(name)
 if data[z:]:
  mods.append(name)
  if data[z:]!=allowed.get(name):errors.append(name+' suffix')
print(json.dumps(dict(frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',checked=len(m),errors=errors,scratch_cfg_appends=mods,lock=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest()),indent=2))
assert not errors
'''
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 with (E/'NBP_SOURCE_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=n,exit=r.returncode,stdout=r.stdout,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if n<10:time.sleep(60)
 else:raise SystemExit('source validation transport exhausted')
(E/'NBP_SOURCE_CHECK.json').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
