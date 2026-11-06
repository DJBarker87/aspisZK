from pathlib import Path
import json,hashlib,subprocess,difflib,base64,lzma
B=Path(__file__).resolve().parent;S=B/'NJT_src';sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((B/'NJT_STAGING_MANIFEST.json').read_text());payload=json.loads(lzma.decompress((B/'NJT_FROZEN_PAYLOAD.json.xz').read_bytes()))
assert sha((B/'NJT_KMX.patch').read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=subprocess.run(['git','apply',str(B/'NJT_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
lib='crates/aspis-r1-cost-probe/src/r1_semantic.rs';program='programs/r1-cost-probe/src/lib.rs'
for n,source in [(lib,'NJT_claims_carrier.rs.txt'),(program,'NJT_claims_carrier_program.rs.txt')]:
 p=S/n;p.write_text(('#![cfg_attr(kani, feature(allocator_api))]\n' if n==program else '')+p.read_text()+'\n'+(B/source).read_text())
pins={n:sha((S/n).read_bytes()) for n in [lib,program,'KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']}
frozen={n:v['sha256'] for n,v in manifest['files'].items() if n not in pins}
for n,h in frozen.items():assert sha((S/n).read_bytes())==h,n
(B/'NJT_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(B/'NJT_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2)+'\n')
patch=''
for n in [lib,program]:patch+=''.join(difflib.unified_diff(base64.b64decode(payload[n]).decode().splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(B/'NJT_NATIVE.patch').write_text(patch)
(B/'NJT_NATIVE_SETUP.json').write_text(json.dumps(dict(kmx_patch_sha256=sha((B/'NJT_KMX.patch').read_bytes()),sources=pins,unchanged_files=len(frozen),cargo_target_dir=str(B/'NJT_target'),scope='data-only one native row ptr::write versus safe reference write, initialized-prefix window; no allocator returning-law or complete129 credit'),indent=2)+'\n')
print('NJM exact KMX and owned one-step native/reference window installed')
