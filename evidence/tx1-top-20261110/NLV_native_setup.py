from pathlib import Path
import json,hashlib,shutil,difflib
B=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads/codex-cx-tx1-prepare-20261110')
S=B/'NLV_src';assert not S.exists(),'Never make another scratch source'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old={}
for n in ['NLJ_SOURCE_PINS.json','NLJ_FROZEN_FILE_PINS.json']:old.update(json.loads((P/n).read_text()))
assert all(sha(P/'NLJ_src'/n)==h for n,h in old.items()),'Predecessor drift'
shutil.copytree(P/'NLJ_src',S)
assert all(sha(S/n)==h for n,h in old.items())
# Apply the owner's amended frozen Pool source in this PRIVATE scratch only.
# Remove only superseded Rust source files; no key/account data is touched.
pool=json.loads((B/'NLV_POOL_FROZEN.json').read_text())
for p in (S/'programs/aspis-pool').rglob('*.rs'):
 n=str(p.relative_to(S))
 if n not in pool['files']:p.unlink();old.pop(n,None)
for n,t in pool['files'].items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
 assert sha(p)==pool['sha256'][n];old[n]=sha(p)
(B/'NLV_POOL_SOURCE_CHECK.json').write_text(json.dumps(dict(revision=pool['revision'],files=pool['sha256'],scope='off-path frozen source only; no Pool bridge or ELF rebuild credit'),indent=2))
expected={n:sha(S/n) for n in ['crates/aspis-r1-cost-probe/src/candidate.rs']}
patch=''
for parent,module,file in [('candidate.rs','NLV_native','NLV_native.rs.txt')]:
 n='crates/aspis-r1-cost-probe/src/'+parent;p=S/n;before=p.read_text()
 p.write_text(before+'\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub(crate) mod '+module+';\n')
 q=p.with_name(module+'.rs');q.write_text((B/file).read_text())
 patch+=''.join(difflib.unified_diff(before.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 patch+='--- /dev/null\n+++ b/'+str(q.relative_to(S))+'\n@@ -0,0 +1,'+str(len(q.read_text().splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in q.read_text().splitlines())
 old[n]=sha(p);old[str(q.relative_to(S))]=sha(q)
(B/'NLV_NATIVE.patch').write_text(patch)
(B/'NLV_SOURCE_PINS.json').write_text(json.dumps(old,indent=2))
(B/'NLV_FROZEN_FILE_PINS.json').write_text('{}')
(B/'NLV_BASE_EXPECTED.json').write_text(json.dumps(expected,indent=2))
shutil.copyfile(P/'NLJ_KMX.patch',B/'NLV_KMX.patch')
(B/'NLV_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P/'NLJ_src'),inherited_pin_files=['NLJ_SOURCE_PINS.json','NLJ_FROZEN_FILE_PINS.json'],bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),kmx_patch_sha256=sha(B/'NLV_KMX.patch')),indent=2))
target=P/'NLJ_target';new=B/'NLV_target'
assert not new.exists() or not any(new.iterdir()),'Never overwrite own nonempty target'
shutil.copytree(target,new,dirs_exist_ok=True)
rows=[]
for f in new.rglob('*'):
 if f.is_file():rows.append(dict(relative=str(f.relative_to(new)),bytes=f.stat().st_size,sha256=sha(f)))
(B/'NLV_NATIVE_TARGET_SEED.json').write_text(json.dumps(dict(source=str(target),bytes=sum(x['bytes'] for x in rows),files=rows),indent=2))
print('Copied frozen source scratch and private target once; cfg-only cut transcriptions installed')
