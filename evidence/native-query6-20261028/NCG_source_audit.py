from NCG_host import *
import base64,zlib
entries=json.loads((E/'NCG_LOCAL_FREEZE.json').read_text())['entries'];data=base64.b64encode(zlib.compress(json.dumps(entries).encode())).decode()
r=py(f'''from pathlib import Path
import json,hashlib,re,base64,zlib
src=Path({B!r})/'NCG_src';rows=json.loads(zlib.decompress(base64.b64decode({data!r})));bad=[];qualified=[]
for row in rows:
 p=src/row['path'];v=p.read_bytes();original=v
 if row['path']=='crates/aspis-r1-cost-probe/src/candidate.rs':
  v=re.sub(rb'\\n#\\[cfg\\(kani\\)\\] #\\[path="(?:NBZ|NCG)_[^"]+\\.rs"\\] mod (?:NBZ|NCG)_[A-Za-z0-9_]+;\\n',b'',v)
  assert hashlib.sha256(v).hexdigest()=='7e51f020af888e6c74ad92932887efacd03e485619ba1fe9350406a9c6936023';qualified.append(dict(path=row['path'],basis='inherited NBW terminal cfg-only harness registrations plus NCG/NBZ registrations'));continue
 if row['path']=='crates/aspis-r1-cost-probe/src/lib.rs':
  assert hashlib.sha256(v).hexdigest()=='04db82c4b8b5d9e46688b1d28f1ad9933b4598e1e144b10dd7cd642b36ab1c87';qualified.append(dict(path=row['path'],basis='unchanged inherited cfg attributes'));continue
 if row['path']=='crates/aspis-r1-cost-probe/src/verifier.rs':
  assert hashlib.sha256(v).hexdigest()=='23c3de16ed408fadfa74d4597345b00da7285ee7b5c5df0058eb4dc6fb65d569';qualified.append(dict(path=row['path'],basis='unchanged inherited NBF/NBO harness registrations'));continue
 if row['path']=='crates/aspis-core/src/field.rs':
  v=v.replace(b'\\n#[cfg(kani)] #[path="NCG_field_arbitrary.rs"] mod NCG_field_arbitrary;\\n',b'')
  v=re.sub(rb'#\\[cfg_attr\\(kani, kani::ensures\\(\\|r:&Option<M31>\\|!?match r\\{{Some\\(v\\)=>v\\.0==u32::from_le_bytes\\(bytes\\)&&v\\.0<P,None=>u32::from_le_bytes\\(bytes\\)>=P\\}}\\)\\)\\]\\n    ',b'',v)
 if row['path']=='crates/aspis-r1-cost-probe/src/fast_pairing.rs':
  v=re.sub(rb'\\n#\\[cfg\\(kani\\)\\] #\\[path="[^"]*/NCG_tail\\.rs"\\] mod NCG_tail;\\n',b'',v)
 if hashlib.sha256(v).hexdigest()!=row['sha256']:bad.append(dict(path=row['path'],actual=hashlib.sha256(v).hexdigest(),expected=row['sha256']))
 if v!=original:qualified.append(dict(path=row['path'],basis='NCG cfg(kani)-only declarations removed; complete remaining bytes frozen'))
print(json.dumps(dict(files=len(rows),mismatches=bad,qualified=qualified),indent=2));assert not bad,bad
''');(E/'NCG_HOST_SOURCE_CHECK.json').write_text(r.stdout);assert r.returncode==0,r.stderr
