from PCA_transport import *
import base64,lzma,hashlib,difflib
sha=lambda b:hashlib.sha256(b).hexdigest()
old=E.parent/'sdk-borrow-20261109'
z=json.loads(lzma.decompress((old/'NLF_FROZEN_INPUTS.json.xz').read_bytes()))
oldpins=json.loads(z['NLF_FROZEN_PINS.json']); files={}
for n,h in oldpins.items():
 raw=base64.b64decode(z['NLF_src/'+n]);assert sha(raw)==h
 if not n.startswith('programs/aspis-pool/'):files[n]=raw
# Complete the existing frozen workspace's non-release member manifests/sources.
extra=['audit/poseidon-pair-probe/program','xtask','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'--',*extra],text=True).splitlines()
for n in paths:
 if n.endswith('.rs') or n.endswith('Cargo.toml'):files[n]=subprocess.check_output(['git','show',rev+':'+n])
poolrev='b936275465600469312d1f058cdc91ea2a11f3dc'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',poolrev,'--','programs/aspis-pool'],text=True).splitlines()
for n in paths:
 if n.endswith('.rs') or n.endswith('Cargo.toml'):files[n]=subprocess.check_output(['git','show',poolrev+':'+n])
assert sha(files['Cargo.lock'])==sha(subprocess.check_output(['git','show',rev+':Cargo.lock']))
pins={n:sha(b) for n,b in files.items()}
(E/'PCA_NATIVE_FROZEN_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
raw=json.dumps({n:base64.b64encode(b).decode() for n,b in files.items()}).encode();(E/'PCA_NATIVE_FROZEN_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'PCA_NATIVE_FROZEN_INPUTS.json.sha256').write_text(sha(raw)+'\n')
patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes();assert sha(patch)=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
(E/'PCA_KMX_copy_stubs.patch').write_bytes(patch)
source=files['programs/aspis-pool/src/pair_forest.rs'].decode();start=source.index('fn require_exact_account_count');end=source.index('\n}',start)+2
body=source[start:end]
reference=body.replace('fn require_exact_account_count','pub(super) fn PCA_count_reference',1)
annotation='#[cfg_attr(kani, kani::ensures(|result| result == &PCA_harness::PCA_count_reference(accounts, expected)))]\n#[cfg_attr(kani, kani::modifies())]\n'
suffix='''\n#[cfg(kani)]
#[allow(non_snake_case)]
mod PCA_harness {
    use super::*;
REFERENCE
    #[kani::proof_for_contract(super::require_exact_account_count)]
    fn PCA_count_contract() {}
}
'''.replace('REFERENCE','\n'.join('    '+l for l in reference.splitlines()))
modified=source[:start]+annotation+source[start:]+suffix
(E/'PCA_native_packets.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),modified.splitlines(True),fromfile='a/programs/aspis-pool/src/pair_forest.rs',tofile='b/programs/aspis-pool/src/pair_forest.rs')))
(E/'PCA_NATIVE_PATCH_META.json').write_text(json.dumps({'source': 'programs/aspis-pool/src/pair_forest.rs','source_sha256':sha(source.encode()),'modified_sha256':sha(modified.encode()),'annotation':annotation,'suffix':suffix,'reference_body_sha256':sha(reference.encode()),'classification':'scratch cfg(kani) contract target only; no repository shipped mutation; exact count helper native signature retained'},indent=1)+'\n')
admission('PCA_NATIVE_SEED')
payload=base64.b64encode(lzma.compress(raw)).decode()
r=ssh('python3',f'''from pathlib import Path
import base64,lzma,json,hashlib,subprocess
b=Path({B!r});s=b/'PCA_src';assert not s.exists()
files=json.loads(lzma.decompress(base64.b64decode({payload!r})))
for n,v in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v))
(b/'PCA_NATIVE_FROZEN_PINS.json').write_text({json.dumps(pins)!r})
(b/'PCA_NATIVE_PATCH_META.json').write_text({(E/'PCA_NATIVE_PATCH_META.json').read_text()!r})
(b/'PCA_KMX_copy_stubs.patch').write_text({patch.decode()!r})
r=subprocess.run(['patch','-p1','-i',str(b/'PCA_KMX_copy_stubs.patch')],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
(s/'programs/aspis-pool/src/pair_forest.rs').write_text({modified!r})
print(json.dumps(dict(frozen_files=len(files),frozen_source_bytes=sum(len(base64.b64decode(v)) for v in files.values()),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),kmx_patch_sha256=hashlib.sha256((b/'PCA_KMX_copy_stubs.patch').read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stderr
(E/'PCA_NATIVE_SEED.json').write_text(r.stdout)
print('Own native scratch seeded from pinned frozen source; exact mitigation and cfg(kani)-only helper contract patch recorded.')
