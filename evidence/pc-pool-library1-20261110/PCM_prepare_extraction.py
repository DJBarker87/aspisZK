"""Materialize route-check inputs exclusively from the frozen Git blobs."""
from pathlib import Path
import subprocess,json,hashlib,lzma,base64,re,posixpath
E=Path(__file__).resolve().parent
old='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';pool='b936275465600469312d1f058cdc91ea2a11f3dc'
paths=['docs/research/v8-r0-zk-20261009/refine/diffharness', 'Cargo.toml','Cargo.lock','crates','programs/aspis-registry','programs/aspis-verifier','programs/r1-cost-probe','audit/poseidon-pair-probe/program','xtask','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon']
files={}
for rev,roots in [(old,paths),(pool,['programs/aspis-pool'])]:
 names=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'--',*roots],text=True).splitlines()
 for name in names:
  assert 'keypair' not in name.lower(),name
  data=subprocess.check_output(['git','show',rev+':'+name]);files[name]=dict(revision=rev,sha256=hashlib.sha256(data).hexdigest(),base64=base64.b64encode(data).decode())
# Known optional path dependencies must still have their committed manifests
# available to Cargo's frozen whole-workspace resolver.
allnames=subprocess.check_output(['git','ls-tree','-r','--name-only',old],text=True).splitlines()
for name in allnames:
 if name.endswith('Cargo.toml') and name not in files:
  data=subprocess.check_output(['git','show',old+':'+name]);files[name]=dict(revision=old,sha256=hashlib.sha256(data).hexdigest(),base64=base64.b64encode(data).decode())
# Cargo validates target paths even for unselected workspace/path packages.
manifest_names=[n for n in files if n.endswith('Cargo.toml')]
for manifest_name in manifest_names:
 directory=posixpath.dirname(manifest_name)
 text=base64.b64decode(files[manifest_name]['base64']).decode()
 targets=['src/lib.rs','src/main.rs','build.rs']+re.findall(r'path\s*=\s*"([^"]+\.rs)"',text)
 for target in targets:
  name=posixpath.normpath(posixpath.join(directory,target))
  if name in allnames and name not in files:
   data=subprocess.check_output(['git','show',old+':'+name]);files[name]=dict(revision=old,sha256=hashlib.sha256(data).hexdigest(),base64=base64.b64encode(data).decode())
raw=json.dumps(files,separators=(',',':')).encode();p=E/'PCM_EXTRACT_INPUTS.json.xz';p.write_bytes(lzma.compress(raw,preset=6))
(E/'PCM_EXTRACT_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(E/'PCM_EXTRACT_SOURCE_MANIFEST.json').write_text(json.dumps({n:{k:v for k,v in r.items() if k!='base64'} for n,r in files.items()},indent=1)+'\n')
assert p.stat().st_size<=20_000_000
print(json.dumps(dict(files=len(files),raw_bytes=len(raw),compressed_bytes=p.stat().st_size,pool_files=sum(n.startswith('programs/aspis-pool/') for n in files))))
