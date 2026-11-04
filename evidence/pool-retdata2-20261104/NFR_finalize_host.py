"""Verify retained task artifacts, then remove only rebuildable own scratch."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
assert not (E/'NFR_ACTIVE.json').exists()
a=[json.loads(l) for l in (E/'NFR_ATTEMPTS.jsonl').read_text().splitlines()]
assert sum(x['kind']=='kani' for x in a)==70
pins=json.loads((E/'NFR_RETAINED.json').read_text())['pins']
elf=json.loads((E/'NFR_ELF_PINS.json').read_text())['pins']
code='''from pathlib import Path
import json,hashlib,shutil
pins=INPUT_PINS
elf=INPUT_ELF
checked=[]
for row in pins+elf:
 p=Path(row['path']);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==row['sha256'],str(p)
 checked.append(dict(path=str(p),sha256=h,size=p.stat().st_size))
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata2-20261104')
assert b.is_dir() and 'cache' not in b.name
assert all((b/f'NFR_K{i:03}/receipt.json').exists() for i in range(1,71))
removed=[]
for name in ['NFR_target','NFR_C_ref_target','NFR_B_objects','NFR_C_objects','NFR_objects','NFO_native','NFR_tmp','NFR_C_ref/target','NFR_C_process_ref/target']:
 p=b/name
 if p.exists():
  assert p.is_dir() and not p.is_symlink();shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(checked=checked,removed_rebuildable_scratch=removed,own_cache_retained=True,elf_rebuilt=False,shipped_sources_changed=False)))
'''.replace('INPUT_PINS',repr(pins)).replace('INPUT_ELF',repr(elf))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFR_FINAL_HOST.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);out['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
(E/'NFR_FINAL_HOST.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(retained_checked=len(pins),elf_pins_checked=len(elf),removed=len(out['removed_rebuildable_scratch']),own_cache_retained=True)))
