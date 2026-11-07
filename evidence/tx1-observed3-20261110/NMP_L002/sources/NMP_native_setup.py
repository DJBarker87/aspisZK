from pathlib import Path
import json,hashlib,shutil,lzma,base64
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-observed2-20261110');S=B/'NMP_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not S.exists(),'Never copy scratch twice'
shutil.copytree(P/'NLZ_src',S)
x=json.loads(lzma.decompress((B/'NMP_FROZEN_INPUTS.json.xz').read_bytes()));rows=[]
for n,v in x.items():
 if n.startswith('NLF_src/'):
  p=S/n.removeprefix('NLF_src/');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
 elif n=='NLF_FROZEN_PINS.json':(B/'NMP_FROZEN_PINS.json').write_text(v)
 elif n=='NLF_KMX_copy_stubs.patch':(B/'NMP_KMX.patch').write_text(v)
frozen=json.loads((B/'NMP_FROZEN_PINS.json').read_text())
for n,h in frozen.items():assert sha(S/n)==h,('frozen',n)
for n,h in json.loads((P/'NLZ_FROZEN_PINS.json').read_text()).items():
 p=P/'NLZ_frozen'/n;assert sha(p)==h;shutil.copyfile(p,S/n)
# Private copied cache; no predecessor directories written.
shutil.copytree(P/'NLZ_target',B/'NMP_target',dirs_exist_ok=True)
(B/'NMP_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P),files=len(frozen),source_bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),target_bytes=sum(p.stat().st_size for p in (B/'NMP_target').rglob('*') if p.is_file()),kmx_sha256=sha(B/'NMP_KMX.patch')),indent=1))
print('Frozen corpus restored; private target copied; KMX pinned')
