from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-tx1-driver2-20261109');S=B/'NLJ_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((B/'NLJ_SOURCE_PINS.json').read_text());assert all(sha(S/n)==h for n,h in old.items())
assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'KMX_stubs.rs')=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
(B/'NLJ_NATIVE_SEED.json').write_text(json.dumps(dict(source=str(P/'NLC_src'),inherited_pin_files=['NLC_SOURCE_PINS.json','NLC_FROZEN_FILE_PINS.json'],bytes=sum(p.stat().st_size for p in S.rglob('*') if p.is_file()),kmx_patch_sha256=sha(B/'NLJ_KMX.patch'),repair='L037 own missing NLC_KMX.patch filename; use exact committed KMX patch'),indent=2))
target=P/'NLC_target';new=B/'NLJ_target'
assert not new.exists() or not any(new.iterdir()),'Never overwrite nonempty own target'
shutil.copytree(target,new,dirs_exist_ok=True)
rows=[]
for f in new.rglob('*'):
 if f.is_file():rows.append(dict(relative=str(f.relative_to(new)),bytes=f.stat().st_size,sha256=sha(f)))
(B/'NLJ_NATIVE_TARGET_SEED.json').write_text(json.dumps(dict(source=str(target),bytes=sum(x['bytes'] for x in rows),files=rows),indent=2))
print('Validated retained partial seed and copied private target; exact committed KMX patch pinned')
