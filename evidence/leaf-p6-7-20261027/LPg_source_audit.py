from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json
old=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027/LPc_src')
new=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-7-20261027/LPg_src')
def scan(p):return {str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.rglob('*') if f.is_file()}
a,b=scan(old),scan(new)
print(json.dumps({'base_tree':str(old),'scratch_tree':str(new),'base_files':len(a),'scratch_files':len(b),'base_manifest_sha256':hashlib.sha256(json.dumps(a,sort_keys=True).encode()).hexdigest(),'scratch_manifest_sha256':hashlib.sha256(json.dumps(b,sort_keys=True).encode()).hexdigest(),'changed':{f:{'base':a[f],'scratch':b[f]} for f in a if f in b and a[f]!=b[f]},'added':{f:b[f] for f in b if f not in a},'removed':[f for f in a if f not in b],'lock_sha256':b['Cargo.lock']},indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90',"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True)
x=json.loads(r.stdout);x['frozen_revision']='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';x['inherited_source_audit']='evidence/leaf-p6-3-20261027/LPc_source-provenance.json';x['instrumentation']='five LPg scratch harness modules plus cfg hooks and contract/Arbitrary attributes; all original computations retained';x['historical_receipt_boundary_note']='LPa and LPc are both inherited bases; the short deps boundary caption omitted LPc but exact source hashes and per-attempt patches include it.'
assert not x['removed'] and len(x['changed'])==5 and len(x['added'])==5,x
assert x['lock_sha256']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
(E/'LPg_source-provenance.json').write_text(json.dumps(x,indent=2)+'\n')
print('source audit',x['base_files'],x['scratch_files'],len(x['changed']),len(x['added']))
