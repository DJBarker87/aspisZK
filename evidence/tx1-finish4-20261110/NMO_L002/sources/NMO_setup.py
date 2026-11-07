from pathlib import Path
import json,hashlib,shutil,difflib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish3-20261110');S=B/'NMO_src'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NMO_PREDECESSOR_SOURCE_PINS.json').read_text())
assert not S.exists()
assert all(H(P/'NMC_src'/n)==h for n,h in pins.items())
shutil.copytree(P/'NMC_src',S)
patch=''
for path,module in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NMO_finish'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','NMO_wire')]:
 p=S/path;before=p.read_text();after=before+'\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub mod '+module+';\n';p.write_text(after)
 q=p.with_name(module+'.rs');q.write_text((B/(module+'.rs')).read_text())
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n'for l in q.read_text().splitlines())
 pins[path]=H(p);pins[str(q.relative_to(S))]=H(q)
(B/'NMO_HARNESSES.patch').write_text(patch)
(B/'NMO_HARNESSES.patch.sha256').write_text(H(B/'NMO_HARNESSES.patch')+'\n')
(B/'NMO_SOURCE_PINS.json').write_text(json.dumps(pins))
assert H(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert not(B/'NMO_target').exists()
shutil.copytree(P/'NMC_target',B/'NMO_target',symlinks=True)
print(json.dumps(dict(status='native_seeded',source_files=len(pins),patch_sha256=H(B/'NMO_HARNESSES.patch'))))
