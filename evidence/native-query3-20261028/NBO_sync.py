from NBO_host import *
import json
import sys
admit(sys.argv[1])
payload=(E/'NBO_native.rs.txt').read_text()
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});src=b/'NBO_src'
old=Path('/home/dombarker/project-offloads/codex-cx-native-query2-20261027/NBF_src')
if not src.exists():src.symlink_to(old,target_is_directory=True)
f=src/'crates/aspis-r1-cost-probe/src/candidate.rs';text=f.read_text();marker='\\n#[cfg(kani)] #[path="NBO_native.rs"] mod NBO_native;\\n'
if marker not in text:f.write_text(text+marker)
(src/'crates/aspis-r1-cost-probe/src/NBO_native.rs').write_text({payload!r})
print(json.dumps(dict(scratch=str(src.resolve()),reuse='symlink to terminal predecessor scratch; no second corpus copy',candidate_sha256=hashlib.sha256(f.read_bytes()).hexdigest())))
''')
assert r.returncode==0,r.stderr
(E/'NBO_SCRATCH.json').write_text(r.stdout)
