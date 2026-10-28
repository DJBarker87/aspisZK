from NBW_host import *
import hashlib
manifest=json.loads(Path('evidence/native-query3-20261028/NBO_FROZEN_SOURCE_MANIFEST.json').read_text())
old=json.loads(Path('evidence/native-query3-20261028/NBO_FINAL_HOST.json').read_text())['scratch_normalized']
expected=dict(manifest)
for name,pin in old.items():expected[name]=pin['scratch_sha256']
code=f'''from pathlib import Path
import json,hashlib
root=Path({B!r})/'NBW_src';expected=json.loads({json.dumps(json.dumps(expected))});bad=[];normalized=[]
for name,sha in expected.items():
 p=root/name;s=p.read_bytes()
 if name=='crates/aspis-r1-cost-probe/src/candidate.rs':
  marker=b'\\n#[cfg(kani)] #[path="NBW_native.rs"] mod NBW_native;\\n'
  assert s.count(marker)==1;s=s.replace(marker,b'');normalized.append(name)
 if name=='crates/aspis-r1-cost-probe/src/lib.rs':
  for marker in [b'#![cfg_attr(kani, recursion_limit = "512")]\\n',b'#![cfg_attr(kani, feature(allocator_api))]\\n']:
   assert s.count(marker)==1;s=s.replace(marker,b'')
  normalized.append(name)
 if hashlib.sha256(s).hexdigest()!=sha:bad.append(name)
print(json.dumps(dict(files=len(expected),unexpected_changes=bad,normalized_only_new_cfg_kani=normalized,inherited_cfg_kani_pins='NBO_FINAL_HOST.json scratch_normalized',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387')))
assert not bad,bad
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -'],input=code,capture_output=True,text=True)
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
(E/'NBW_HOST_FREEZE.json').write_text(r.stdout)
assert r.returncode==0,r.stderr
print(r.stdout)
