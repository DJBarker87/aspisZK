from pathlib import Path
import json,hashlib,shutil,difflib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-finish3-20261110');S=B/'NMO_src'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((B/'NMO_PREDECESSOR_SOURCE_PINS.json').read_text())
assert S.exists()
pins=json.loads((B/'NMO_SOURCE_PINS.json').read_text())
for path,module in [('crates/aspis-r1-cost-probe/src/r1_wire.rs','NMO_wire'),('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NMO_stage')]:
 p=S/path
 suffix='\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub mod '+module+';\n'
 if not p.read_text().endswith(suffix) and module=='NMO_stage':p.write_text(p.read_text()+suffix)
 q=p.with_name(module+'.rs');q.write_text((B/(module+'.rs')).read_text());pins[path]=H(p);pins[str(q.relative_to(S))]=H(q)
(B/'NMO_SOURCE_PINS.json').write_text(json.dumps(pins))
patch=''
for path in ['crates/aspis-r1-cost-probe/src/r1_semantic.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs']:
 before=(P/'NMC_src'/path).read_text();after=(S/path).read_text()
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
for module in ['NMO_finish','NMO_stage','NMO_wire']:
 path='crates/aspis-r1-cost-probe/src/'+module+'.rs';q=S/path
 patch+='--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n'for l in q.read_text().splitlines())
(B/'NMO_HARNESSES.patch').write_text(patch);(B/'NMO_HARNESSES.patch.sha256').write_text(H(B/'NMO_HARNESSES.patch')+'\n')
print('Installed claims-error partition and owned hash decomposition; frozen bodies unchanged')
