from pathlib import Path
import tempfile,base64,json,lzma,subprocess,hashlib
E=Path(__file__).resolve().parent
f=json.loads(lzma.decompress((E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz').read_bytes()))
with tempfile.TemporaryDirectory(prefix='NLQ_patch_') as t:
 for name,value in f.items():
  if name.startswith('NLF_src/'):
   p=Path(t)/name.removeprefix('NLF_src/');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(value))
 r=subprocess.run(['git','apply','--check',str(E/'NLQ_NATIVE.patch')],cwd=t,capture_output=True,text=True)
 (E/'NLQ_PATCH_CHECK.json').write_text(json.dumps(dict(exit_status=r.returncode,stderr=r.stderr,patch_sha256=hashlib.sha256((E/'NLQ_NATIVE.patch').read_bytes()).hexdigest()),indent=1)+'\n')
 assert r.returncode==0,r.stderr
print('Scratch patch preflight PASS')
