from NEW_remote import *
import json,lzma
assert not(E/'NEW_ACTIVE.json').exists()
p=json.loads(lzma.decompress((E/'NEW_PEER_NEV.json.xz').read_bytes()))
key='evidence/slice-q-mul3-20261103/NEV_NATIVE_LIBRARY_PINS.json'
pins=json.loads(p['blobs'][p['files'][key]['blob']]['content'])
a='NEW_STD_LIBRARY_INPUT';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import json,hashlib
pins={pins!r};result={{'library':[],'sources':{{}}}}
for item in pins['objects']:
 p=Path(item['path']);h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b)
 assert h.hexdigest()==item['sha256'],str(p)
 result['library'].append(item)
print(json.dumps(result))
''');assert r.returncode==0,r.stderr
v=json.loads(r.stdout)
for name,item in v['sources'].items():
 dest='NEW_STD_'+name.replace('/','_')+'.txt';(E/dest).write_text(item.pop('source'));item['artifact']=dest
src=E/'NEW_STD_core_src_slice_iter_macros.rs.txt'
import hashlib
v['sources']['core/src/slice/iter/macros.rs']=dict(artifact=src.name,sha256=hashlib.sha256(src.read_bytes()).hexdigest(),url='https://raw.githubusercontent.com/rust-lang/rust/53732d5e0/library/core/src/slice/iter/macros.rs',qualification='Upstream rustc commit context; native compiler/library artifact hashes verified separately, exactly as NEV library pins')
(E/'NEW_STD_LIBRARY_PINS.json').write_text(json.dumps(v,indent=1)+'\n')
