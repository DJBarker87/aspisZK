"""Allocate the remaining named, distinct audit groups within140 scopes."""
from pathlib import Path
import json,sys,subprocess
E=Path(__file__).resolve().parent;last=int(sys.argv[1]);start=last+1;raw_start=start+8;groups=136-raw_start;assert groups>0
subprocess.run([sys.executable,str(E/'NLZ_prepare_audit.py'),str(groups)],check=True)
B='/home/dombarker/project-offloads/codex-cx-tx1-observed2-20261110';T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
env=dict(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR=B+'/NLZ_tmp',CARGO_TARGET_DIR=B+'/NLZ_target',LEAN_PATH=':'.join(json.loads((E/'NLZ_PATHS.json').read_text())))
plan=[]
def write(n,kind,module,sources,command,**kw):
 a=f'NLZ_L{n:03}';x=dict(attempt=a,kind=kind,module=module,sources=sources,command=command,env=env,timeout=180,**kw);assert not(E/a/'receipt.json').exists();(E/(a+'.json')).write_text(json.dumps(x));plan.append(a)
inputs=['NLZ_audit_setup.py','NLZ_MODULES.json','NLZ_AUDIT_ROOTS.json','NLZ_AUDIT_MODULES.json','NLZ_EXPECTED_IMPORTS.jsonl','NLZ_AUDIT_MANIFEST_PINS.json','NLZ_native/NFA_WALKER.c','NLZ_native/NFA_MemoryLimit.c','NLZ_WALKER.lean.txt','NLZ_WALKER_PINS.json']
write(start,'setup','NLZ_audit_setup',inputs,['python3','NLZ_audit_setup.py'],collect=['NLZ_PROOF_SOURCE.json'],expected_time='Freeze own successful sources and once-uploaded audit inputs; no compilation')
for k,name in enumerate(['NLZ_COMBINED_IMPORT','NLZ_Driver','NLZ_ProofDriver'],1):
 src='NLZ_generated/'+name+'.lean';cmd=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NLZ_generated','-o','NLZ_objects/'+name+'.olean',src]
 kw={}
 if name!='NLZ_COMBINED_IMPORT':cmd+=['-c','NLZ_native/'+name+'.c'];kw['collect']=['NLZ_native/'+name+'.c']
 write(start+k,'lean',name,[src],cmd,expected_time='One focused audit module; combined import executed once',**kw)
for k,name in enumerate(['NLZ_Driver','NLZ_ProofDriver'],4):
 write(start+k,'link',name,['NLZ_native/'+name+'.c','NLZ_native/NFA_WALKER.c','NLZ_native/NFA_MemoryLimit.c','NLZ_link.py'],['python3','NLZ_link.py',name],collect=[name+'_BINARY_PIN.json'],expected_time='Optimized C compilation/link of existing audit method; no proof replay')
for n,mode in [(start+6,'fixtures'),(start+7,'scan')]+[(raw_start+j,'proof'+str(j))for j in range(groups)]:
 sources=['NLZ_generated/NLZ_ProofDriver.lean','NLZ_generated/NLZ_Driver.lean','NLZ_audit_batch.py','NLZ_AUDIT_MANIFEST_PINS.json']
 kw=dict(collect_globs=['NLZ_audit/'+mode+'/*'])
 if mode=='scan':kw['collect']=['NLZ_LOADED_scan.jsonl']
 write(n,'audit','NLZ_COMBINED_IMPORT',sources,['python3','NLZ_audit_batch.py',mode],expected_time='One distinct raw ax2 slice or NFX scan; smaller groups avoid predecessor packaging timeout',**kw)
(E/'NLZ_AUDIT_PLAN.json').write_text(json.dumps(dict(start=start,raw_start=raw_start,groups=groups,attempts=plan,combined_audits=1,final_reserved=[f'NLZ_L{j:03}'for j in range(136,141)]),indent=2))
print(json.dumps(dict(audit_start=start,groups=groups,raw_end=135,final_reserved=5)))
