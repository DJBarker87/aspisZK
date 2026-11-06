from pathlib import Path
import json,hashlib,subprocess,difflib,base64,lzma
B=Path(__file__).resolve().parent;S=B/'NJM_src';sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((B/'NJM_STAGING_MANIFEST.json').read_text());payload=json.loads(lzma.decompress((B/'NJM_FROZEN_PAYLOAD.json.xz').read_bytes()))
assert sha((B/'NJM_KMX.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=subprocess.run(['git','apply',str(B/'NJM_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
lib='crates/aspis-r1-cost-probe/src/r1_semantic.rs';program='programs/r1-cost-probe/src/lib.rs'
for n,source in [(lib,'NJM_claims_window.rs.txt'),(program,'NJM_claims_program.rs.txt')]:
 p=S/n;p.write_text(p.read_text()+'\n'+(B/source).read_text())
pins={n:sha((S/n).read_bytes()) for n in [lib,program,'KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']}
frozen={n:v['sha256'] for n,v in manifest['files'].items() if n not in pins}
for n,h in frozen.items():assert sha((S/n).read_bytes())==h,n
(B/'NJM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(B/'NJM_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2)+'\n')
patch=''
for n in [lib,program]:patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJM_NATIVE.patch').write_text(patch)
(B/'NJM_NATIVE_SETUP.json').write_text(json.dumps(dict(kmx_patch_sha256=sha((B/'NJM_KMX.patch').read_bytes()),sources=pins,unchanged_files=len(frozen),cargo_target_dir=str(B/'NJM_target'),scope='data-only one native row ptr::write versus safe reference write, initialized-prefix window; no allocator returning-law or complete129 credit'),indent=2)+'\n')
print('NJM exact KMX and owned one-step native/reference window installed')
