"""Own scratch setup from pinned retained NHR payload, inside capped scope."""
from pathlib import Path
import json,lzma,hashlib,base64,subprocess,difflib
B=Path(__file__).resolve().parent;S=B/'NHW_src'
R=B.parent/'codex-cx-extract-stage-20261106'
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((R/'NHR_STAGING_MANIFEST.json').read_text())
assert manifest['revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
raw=lzma.decompress((R/'NHR_FROZEN_PAYLOAD.json.xz').read_bytes())
assert sha(raw)==(R/'NHR_FROZEN_PAYLOAD.json.sha256').read_text().strip()
payload=json.loads(raw);assert set(payload)==set(manifest['files'])
for n,info in manifest['files'].items():
 data=base64.b64decode(payload[n],validate=True);assert sha(data)==info['sha256']
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==info['git_blob']
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True)
 assert not p.exists(),n
 p.write_bytes(data)
patch=(B/'NHW_KMX.patch').read_bytes();assert sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=subprocess.run(['patch','-p1','--batch'],input=patch,cwd=S,capture_output=True);assert r.returncode==0,r.stderr
p=S/'crates/aspis-r1-cost-probe/src/lib.rs';before=p.read_text();after='#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\n#[allow(non_snake_case)]\nmod NHW_window;\n';p.write_text(after)
q=p.parent/'NHW_window.rs';q.write_text((B/'NHW_window.rs.txt').read_text())
diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/lib.rs',tofile='b/crates/aspis-r1-cost-probe/src/lib.rs'))
diff+=''.join(difflib.unified_diff([],q.read_text().splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHW_window.rs'))
(B/'NHW_HARNESS.patch').write_text(diff)
pins={str(p.relative_to(S)):sha(p.read_bytes()) for p in S.rglob('*') if p.is_file()}
(B/'NHW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(B/'NHW_NATIVE_SETUP.json').write_text(json.dumps(dict(frozen_revision=manifest['revision'],input_sha256=sha(raw),kmx_patch_sha256=sha(patch),files=len(pins),source_bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),harness_patch_sha256=sha(diff.encode()),no_extraction=True),indent=1)+'\n')
print((B/'NHW_NATIVE_SETUP.json').read_text())
