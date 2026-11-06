from pathlib import Path
import json,hashlib,shutil,difflib,lzma
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109');S=B/'NLI_src'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not S.exists(),'Never create a second scratch tree'
pins=json.loads((B/'NLI_PREDECESSOR_SOURCE_PINS.json').read_text())
assert all((P/'NLC_src'/n).is_file() and H(P/'NLC_src'/n)==h for n,h in pins.items()),'Predecessor drift'
shutil.copytree(P/'NLC_src',S)
assert H(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
patch='';beforepins=dict(pins)
for n,module,file in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NLI_rounds','NLI_rounds.rs.txt'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','NLI_factory','NLI_factory.rs.txt'),('programs/r1-cost-probe/src/lib.rs','NLI_program','NLI_program.rs.txt')]:
 p=S/n;before=p.read_text();after=before+'\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub mod '+module+';\n';p.write_text(after)
 q=p.with_name(module+'.rs');q.write_text((B/file).read_text())
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in q.read_text().splitlines())
 pins[n]=H(p);pins[str(q.relative_to(S))]=H(q)
# Retained target objects copied once; no writes to the predecessor target.
target=P/'NLC_target';targetbytes=sum(p.stat().st_size for p in target.rglob('*') if p.is_file())
assert targetbytes<10_000_000_000,'Do not fill disk with a large target seed'
assert not (B/'NLI_target').exists()
shutil.copytree(target,B/'NLI_target',symlinks=True)
seed=[]
for p in (B/'NLI_target').rglob('*'):
 if p.is_file():seed.append(dict(path=str(p.relative_to(B)),sha256=H(p),bytes=p.stat().st_size))
blob=json.dumps(dict(files=seed,bytes=targetbytes),indent=1).encode();(B/'NLI_NATIVE_CACHE_PINS.json.xz').write_bytes(lzma.compress(blob));(B/'NLI_NATIVE_CACHE_PINS.json.sha256').write_text(hashlib.sha256(blob).hexdigest()+'\n')
(B/'NLI_NATIVE.patch').write_text(patch);(B/'NLI_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1));(B/'NLI_FROZEN_FILE_PINS.json').write_text('{}')
(B/'NLI_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P/'NLC_src'),source_files=len(beforepins),source_bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),target_source=str(target),target_seed_bytes=targetbytes,lock_sha256=H(S/'Cargo.lock'),CARGO_TARGET_DIR=str(B/'NLI_target'),kmx_patch_sha256=H(B/'NLI_KMX.patch')),indent=1))
print(json.dumps(dict(source_files=len(beforepins),target_bytes=targetbytes,patch_sha256=H(B/'NLI_NATIVE.patch'))))
