from pathlib import Path
import subprocess,json,hashlib,difflib,lzma
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-front2b-20261028'
# Immutable Git objects only; no other worktree is read.
tree={}
for line in subprocess.check_output(['git','ls-tree','-r',F],text=True).splitlines():
 meta,n=line.split('\t',1)
 if n.endswith('.rs') or Path(n).name in ['Cargo.toml','Cargo.lock','rust-toolchain','rust-toolchain.toml'] or n.endswith(('.cargo/config','.cargo/config.toml')):tree[n]=meta.split()[2]
code='''from pathlib import Path
import json,hashlib
b=Path(B);s=b/'NDN_src';frozen=json.loads(PAYLOAD);out={};pins=json.loads((b/'NDN_SOURCE_PINS.json').read_text())
for p in s.rglob('*'):
 if not p.is_file():continue
 n=str(p.relative_to(s))
 if n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:continue
 if not (n.endswith('.rs') or p.name in ['Cargo.toml','Cargo.lock','rust-toolchain','rust-toolchain.toml'] or n.endswith(('.cargo/config','.cargo/config.toml'))):continue
 data=p.read_bytes();oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()
 if frozen.get(n)!=oid:out[n]=data.decode()
print(json.dumps(dict(changed=out,pins=pins)))
'''.replace('B',repr(B),1).replace('PAYLOAD',repr(json.dumps(tree)))
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);changed=x['changed'];(E/'NDN_FINAL_HOST_PINS.json').write_text(json.dumps(x['pins'],indent=2)+'\n')
# Select the immutable final local generator repair, not the stale failing upload.
import sys;sys.path.insert(0,str(E));from NDN_patch import files
changed.update(files())
def original(n):
 r=subprocess.run(['git','show',F+':'+n],capture_output=True);return r.stdout.decode() if r.returncode==0 else ''
def patch(src,name):
 out=''
 for n,data in sorted(src.items()):
  prior=original(n)
  if prior==data:continue
  out+=''.join(difflib.unified_diff(prior.splitlines(True),data.splitlines(True),fromfile='a/'+n if n in tree else '/dev/null',tofile='b/'+n,n=0))
 p=E/name;p.write_text(out);(E/(name+'.sha256')).write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+name+'\n')
patch(changed,'NDN_harness.patch')
# Exact tested configuration for the sole new local closure, independently reproducible.
initial=json.loads(lzma.decompress((E/'NDN_K001-input-pins.json.xz').read_bytes()))
archive={}
old=E.parent/'native-front2-20261028/NDE_K080/sources/NDE_src'
for p in old.rglob('*.rs'):archive[str(p.relative_to(old))]=p.read_text()
for p in (E/'NDN_K001/sources/NDN_src').rglob('*.rs'):archive[str(p.relative_to(E/'NDN_K001/sources/NDN_src'))]=p.read_text()
tested={}
for n,data in changed.items():
 if n not in initial:continue
 data=archive.get(n,data)
 assert hashlib.sha256(data.encode()).hexdigest()==initial[n],('cannot reproduce tested source',n)
 tested[n]=data
patch(tested,'NDN_PACKED_TESTED.patch')
(E/'NDN_PATCH_AUDIT.json').write_text(json.dumps(dict(frozen=F,final_repair_verified=False,repair_reason='cfg statement blocks; Kani budget exhausted',tested_attempt='NDN_K001',tested_patch='NDN_PACKED_TESTED.patch',kmx_apply_first='evidence/kani-mitig-20261028/KMX_copy_stubs.patch',kmx_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',apply='git apply --unidiff-zero; scratch copy only',final_files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in changed.items()},tested_files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in tested.items()}),indent=2)+'\n')
print('Exported',len(changed),'final scratch delta files;',len(tested),'exact tested packed files')
