from NBZ_host import *
import sys,fcntl,hashlib,difflib
_serial=(E/'NBZ_SERIAL.lock').open('a');fcntl.flock(_serial,fcntl.LOCK_EX)
attempt,name,local=sys.argv[1:];assert name.startswith('NBZ_')
admit(attempt)
s=Path(local).read_text()
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});p=b/'NBZ_src/crates/aspis-r1-cost-probe/src'
(p/{(name+'.rs')!r}).write_text({s!r})
f=p/'candidate.rs';s=f.read_text();marker='\\n#[cfg(kani)] #[path="{name}.rs"] mod {name};\\n'
if marker not in s:f.write_text(s+marker)
print(json.dumps(dict(source_sha256=hashlib.sha256((p/{(name+'.rs')!r}).read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256(f.read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stderr
(E/(attempt+'-source.json')).write_text(r.stdout)
