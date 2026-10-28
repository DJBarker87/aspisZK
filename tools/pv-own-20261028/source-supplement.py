from pathlib import Path
import subprocess,hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-own-20261028'
p='crates/aspis-core/src/field.rs';b=(R/p).read_bytes()
code='''from pathlib import Path
import hashlib,json
field=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/crates/aspis-core/src/field.rs')
assert hashlib.sha256(field.read_bytes()).hexdigest()==FIELDHASH
lib=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
rows=[]
for rel in ['alloc/src/vec/mod.rs','alloc/src/raw_vec/mod.rs','alloc/src/string.rs','alloc/src/boxed.rs','std/src/path.rs']:
 p=lib/rel;b=p.read_bytes();s=b.decode();rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),drop_lines=[dict(line=i+1,text=x) for i,x in enumerate(s.splitlines())if 'Drop for' in x or 'drop_in_place(' in x]))
print(json.dumps(dict(field_sha256=FIELDHASH,checked_after_native_scope=True,stdlib=rows,classification='supplemental source check, not historical pre-compile pin or universal source/world law'),indent=2))
'''.replace('FIELDHASH',repr(hashlib.sha256(b).hexdigest()))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'source-supplement.json').write_text(r.stdout);print('Field source matches current candidate; check explicitly recorded after native probe')
