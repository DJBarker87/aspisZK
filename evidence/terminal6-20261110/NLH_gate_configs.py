from pathlib import Path
import sys,json
p=Path(__file__).resolve().parent;start=int(sys.argv[1]);groups=len(json.loads((p/'NLH_AUDIT_ROOTS.json').read_text())['groups']);T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0';env=json.loads((p/'NLH_ENV.json').read_text());env.update(LEAN_SYSROOT=T,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',TMPDIR='/home/dombarker/project-offloads/codex-cx-terminal6-20261110/NLH_tmp')
base=['NLH_seed.py','NLH_SEED_INPUTS.json','NLH_GATE_SOURCES.json','NLH_AUDIT_ROOTS.json','NLH_AUDIT_MODULES.json','NLH_EXPECTED_IMPORTS.jsonl'];mapping={}
modes=['driver','link','combined','fixtures','scan']+['proof'+str(i)for i in range(groups)]
for i,mode in enumerate(modes,start):
 a=f'NLH_L{i:03}';x=dict(attempt=a,kind='audit',module='NLH_'+mode,sources=base.copy(),env=env,timeout=180,expected_time='One capped focused '+mode+' gate partition; no cold dependency rebuild',audit_modules=['NKW_COMBINED_IMPORT','NKY_COMBINED_IMPORT','NFA_WALKER','NFA_MemoryLimit'])
 if mode=='driver':x.update(kind='lean',module='NLH_Driver',command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.','-o','NLH_objects/NLH_Driver.olean','-c','NLH_native/NLH_Driver.c','NLH_Driver.lean']);x['sources']=['NLH_Driver.lean']+base
 elif mode=='link':x['command']=['python3','NLH_link.py'];x['sources']=['NLH_link.py','NLH_ProofDriver.lean','NLH_DRIVER_INPUTS.json','NLH_WALKER_IDENTITY.json','NLH_WALKER_SOURCE.lean.txt']+base;x['collect']=['NLH_LINK.json','NLH_Driver-link.log','NLH_Driver-link.time']
 elif mode=='combined':x.update(kind='lean',module='NLH_COMBINED_IMPORT',command=[T+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','.','-o','NLH_objects/NLH_COMBINED_IMPORT.olean','NLH_COMBINED_IMPORT.lean']);x['sources']=['NLH_COMBINED_IMPORT.lean']+base
 else:
  x['command']=['python3','NLH_batch.py',mode,a];x['sources']=['NLH_batch.py']+base;x['collect_globs']=['NLH_audit/'+mode+'/*'];x['audit_modules']+=['NLH_COMBINED_IMPORT']
 (p/(a+'.json')).write_text(json.dumps(x));mapping[mode]=a
(p/'NLH_GATE_ATTEMPTS.json').write_text(json.dumps(mapping,indent=1)+'\n');print(json.dumps(dict(scopes=len(modes),first=mapping['driver'],last=mapping[modes[-1]])))
