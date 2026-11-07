from pathlib import Path
import json,hashlib,difflib,subprocess
B=Path(__file__).resolve().parent;S=B/'NMC_src'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prior=json.loads((B/'NMC_PREDECESSOR_SOURCE_PINS.json').read_text())
pins=json.loads((B/'NMC_SOURCE_PINS.json').read_text());patch='';files=[]
for path,module in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NMC_segments'),('programs/r1-cost-probe/src/lib.rs','NMC_program')]:
 p=S/path;after=p.read_text();tail='\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub mod '+module+';\n'
 assert after.endswith(tail);before=after[:-len(tail)];assert hashlib.sha256(before.encode()).hexdigest()==prior[path]
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 q=p.with_name(module+'.rs');assert H(q)==pins[str(q.relative_to(S))]
 body=q.read_text();patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+line+'\n'for line in body.splitlines())
 files.append(dict(path=str(q.relative_to(S)),sha256=H(q),bytes=q.stat().st_size))
p=B/'NMC_HARNESSES.patch'
if p.exists():assert p.read_text()==patch,'Final patch differs from the pinned current harness inputs'
p.write_text(patch)
subprocess.run(['git','apply','--reverse','--check',str(p)],cwd=S,check=True,capture_output=True)
(B/'NMC_HARNESSES.patch.sha256').write_text(H(p)+'\n')
(B/'NMC_PATCH_EXPORT.json').write_text(json.dumps(dict(basis='verified byte-identical NLU scratch predecessor; predecessor pins committed',files=files,patch_sha256=H(p),reverse_apply_check=True,source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_lock_sha256=H(S/'Cargo.lock')),indent=2)+'\n')
print(json.dumps(dict(status='PASS_PATCH_EXPORT',files=len(files),bytes=p.stat().st_size)))
