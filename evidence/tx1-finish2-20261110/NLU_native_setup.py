from pathlib import Path
import json,hashlib,shutil,difflib,lzma
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish-20261110');S=B/'NLU_src'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not S.exists(),'Never create a second scratch tree'
pins=json.loads((B/'NLU_PREDECESSOR_SOURCE_PINS.json').read_text())
assert all((P/'NLI_src'/n).is_file() and H(P/'NLI_src'/n)==h for n,h in pins.items()),'Predecessor drift'
shutil.copytree(P/'NLI_src',S)
assert H(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
n='programs/r1-cost-probe/src/lib.rs';p=S/n;before=p.read_text();after=before+'\n#[cfg(kani)]\n#[path = "NLU_program.rs"]\npub mod NLU_program;\n';p.write_text(after)
q=p.with_name('NLU_program.rs');q.write_text((B/'NLU_program.rs.txt').read_text())
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in q.read_text().splitlines())
pins[n]=H(p);pins[str(q.relative_to(S))]=H(q)
# Warm target copied from NLC rather than the larger NLI target.
target=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109/NLC_target')
size=sum(p.stat().st_size for p in target.rglob('*') if p.is_file());assert size<2000000000
assert not (B/'NLU_target').exists();shutil.copytree(target,B/'NLU_target',symlinks=True)
(B/'NLU_NATIVE.patch').write_text(patch);(B/'NLU_SOURCE_PINS.json').write_text(json.dumps(pins));(B/'NLU_FROZEN_FILE_PINS.json').write_text('{}')
(B/'NLU_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P/'NLI_src'),target_source=str(target),target_seed_bytes=size,CARGO_TARGET_DIR=str(B/'NLU_target'),lock_sha256=H(S/'Cargo.lock'),kmx_stubs_sha256=H(S/'KMX_stubs.rs'))))
print(json.dumps(dict(files=len(pins),target_seed_bytes=size)))
