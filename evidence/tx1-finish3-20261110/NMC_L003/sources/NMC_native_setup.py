from pathlib import Path
import json,hashlib,shutil,difflib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish2-20261110');S=B/'NMC_src'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not S.exists()
pins=json.loads((B/'NMC_PREDECESSOR_SOURCE_PINS.json').read_text())
assert all(H(P/'NLU_src'/n)==h for n,h in pins.items())
shutil.copytree(P/'NLU_src',S)
patch=''
for path,module in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NMC_segments'),('programs/r1-cost-probe/src/lib.rs','NMC_program')]:
 p=S/path;before=p.read_text();after=before+'\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub mod '+module+';\n';p.write_text(after)
 q=p.with_name(module+'.rs');q.write_text((B/(module+'.rs.txt')).read_text())
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in q.read_text().splitlines())
 pins[path]=H(p);pins[str(q.relative_to(S))]=H(q)
assert H(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(B/'NMC_NATIVE.patch').write_text(patch)
(B/'NMC_SOURCE_PINS.json').write_text(json.dumps(pins))
(B/'NMC_FROZEN_FILE_PINS.json').write_text('{}')
target=P/'NLU_target';size=sum(p.stat().st_size for p in target.rglob('*') if p.is_file());assert size<2_000_000_000
assert not (B/'NMC_target').exists();shutil.copytree(target,B/'NMC_target',symlinks=True)
(B/'NMC_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P/'NLU_src'),source_files=len(pins),target_seed_bytes=size,lock_sha256=H(S/'Cargo.lock'))))
print(json.dumps(dict(files=len(pins),target_seed_bytes=size)))
