from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json
old=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-7-20261027/LPg_src')
new=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027/LPh_src')
removed={}
for f in ['verifier.rs','compact.rs','r1_wire.rs']:
 for suffix in ['.orig','.rej']:
  p=new/'crates/aspis-r1-cost-probe/src'/(f+suffix)
  if p.exists():removed[str(p.relative_to(new))]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size};p.unlink()
def scan(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.rglob('*') if f.is_file()}
a,b=scan(old),scan(new)
changed={f:{'base':a[f],'scratch':b[f]} for f in a if f in b and a[f]!=b[f]}
def computation(p):return [l for l in p.read_text().splitlines() if l.strip() and 'kani' not in l]
checks={f:computation(old/f)==computation(new/f) for f in changed}
print(json.dumps({'base_tree':str(old),'scratch_tree':str(new),'base_files':len(a),'scratch_files':len(b),'base_manifest_sha256':hashlib.sha256(json.dumps(a,sort_keys=True).encode()).hexdigest(),'scratch_manifest_sha256':hashlib.sha256(json.dumps(b,sort_keys=True).encode()).hexdigest(),'changed':changed,'added':{f:b[f] for f in b if f not in a},'removed':[f for f in a if f not in b],'parent_computation_lines_equal_after_cfg_instrumentation_filter':checks,'discarded_owned_patch_tool_backups':removed,'lock_sha256':b['Cargo.lock']},indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90',"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True)
x=json.loads(r.stdout);x.update(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',inherited_source_audit='evidence/leaf-p6-7-20261027/LPg_source-provenance.json',instrumentation='six LPh scratch harness modules, cfg-only parent hooks, inherited cfg contract instrumentation removed only where incompatible with manual raw stubbing')
assert not x['removed'] and len(x['changed'])==6 and len(x['added'])==6,x
assert all(x['parent_computation_lines_equal_after_cfg_instrumentation_filter'].values()),x
assert x['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
for name in ['crates','programs','Cargo.lock']:
 frozen=subprocess.check_output(['git','rev-parse',x['frozen_revision']+':'+name],text=True).strip();current=subprocess.check_output(['git','rev-parse','HEAD:'+name],text=True).strip();assert frozen==current,(name,frozen,current)
 x.setdefault('research_frozen_git_objects',{})[name]={'frozen':frozen,'current':current,'identical':True}
(E/'LPh_source-provenance.json').write_text(json.dumps(x,indent=2)+'\n')
print('source audit',x['base_files'],x['scratch_files'],len(x['changed']),len(x['added']))
