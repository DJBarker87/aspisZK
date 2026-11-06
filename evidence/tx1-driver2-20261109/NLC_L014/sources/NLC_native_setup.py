from pathlib import Path
import json,hashlib,shutil,difflib
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver-20261108')
S=B/'NLC_src'; assert not S.exists(),'Never create another scratch tree'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old={}
for n in ['NKQ_SOURCE_PINS.json','NKQ_FROZEN_FILE_PINS.json']:
 old.update(json.loads((P/n).read_text()))
assert all(sha(P/'NKQ_src'/n)==h for n,h in old.items()),'Predecessor source drift'
shutil.copytree(P/'NKQ_src',S)
assert all(sha(S/n)==h for n,h in old.items()),'Seed copy drift'
patch=''
for parent,module,file in [('r1_semantic.rs','NLC_native','NLC_native.rs.txt'),('r1_wire.rs','NLC_factory','NLC_factory.rs.txt')]:
 n='crates/aspis-r1-cost-probe/src/'+parent;p=S/n;before=p.read_text()
 p.write_text(before+'\n#[cfg(kani)]\npub(crate) mod '+module+';\n')
 q=p.with_name(module+'.rs');q.write_text((B/file).read_text())
 patch+=''.join(difflib.unified_diff(before.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in q.read_text().splitlines())
 old[n]=sha(p);old[str(q.relative_to(S))]=sha(q)
(B/'NLC_NATIVE.patch').write_text(patch)
(B/'NLC_SOURCE_PINS.json').write_text(json.dumps(old,indent=2))
(B/'NLC_FROZEN_FILE_PINS.json').write_text('{}')
(B/'NLC_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P/'NKQ_src'),inherited_pin_files=['NKQ_SOURCE_PINS.json','NKQ_FROZEN_FILE_PINS.json'],bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),kmx_patch_sha256=sha(P/'NKQ_KMX.patch')),indent=2))
print('Copied and pinned predecessor source once; installed cfg-only NLC windows')
