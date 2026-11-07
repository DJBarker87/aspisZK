from pathlib import Path
import json,shutil,hashlib,difflib
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-observed-20261110');S=B/'NLZ_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not S.exists(),'Never copy scratch twice'
shutil.copytree(P/'NLR_src',S)
frozen=json.loads((B/'NLZ_FROZEN_PINS.json').read_text())
for n,h in frozen.items():
 p=B/'NLZ_frozen'/n;assert sha(p)==h;shutil.copyfile(p,S/n)
# No inherited harness entry is added to changed frozen files. Other inherited modules are untouched.
patch='';expected={n:sha(S/n) for n in frozen if n!='Cargo.lock'}
for parent,mod in [('r1_semantic.rs','NLZ_native'),('r1_wire.rs','NLZ_factory')]:
 n='crates/aspis-r1-cost-probe/src/'+parent;p=S/n;before=p.read_text();p.write_text(before+'\n#[cfg(kani)]\n#[path = "'+mod+'.rs"]\npub(crate) mod '+mod+';\n');q=p.with_name(mod+'.rs');q.write_text((B/(mod+'.rs.txt')).read_text())
 patch+=''.join(difflib.unified_diff(before.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in q.read_text().splitlines())
(B/'NLZ_NATIVE.patch').write_text(patch)
allpins={str(p.relative_to(S)):sha(p) for root in [S/'crates',S/'programs'] for p in root.rglob('*') if p.is_file()}
(B/'NLZ_SOURCE_PINS.json').write_text(json.dumps(allpins,indent=2));(B/'NLZ_FROZEN_FILE_PINS.json').write_text('{}');(B/'NLZ_BASE_EXPECTED.json').write_text(json.dumps(expected,indent=2))
shutil.copyfile(P/'NLR_KMX.patch',B/'NLZ_KMX.patch')
shutil.copytree(P/'NLR_target',B/'NLZ_target',dirs_exist_ok=True)
print('Private source/target copied; frozen bodies restored with cfg-only NLZ harness hooks')
