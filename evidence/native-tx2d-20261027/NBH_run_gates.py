from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[('NBH_K006','pair_terminal::NBH_after::NBH_exact8'),('NBH_K007','pair_terminal::NBH_after::NBH_exact32')]
for v in [1,2]:
 for entry in [False,True]:
  jobs.append((f'NBH_K{len(jobs)+6:03}','verifier_registry::NBH_registry::NBH_validate_verifier_registry_'+('entry_' if entry else '')+'v'+str(v)+'_gate'))
jobs.append(('NBH_K012','verifier_registry::NBH_registry::NBH_zero_gate'))
for v,entry in [(1,False),(1,True),(2,False),(2,True)]:
 jobs.append((f'NBH_K{len(jobs)+6:03}','verifier_registry::NBH_registry::NBH_decode_verifier_registry_'+('entry_' if entry else '')+'v'+str(v)+'_gate'))
for name in ['policy','identity','policy_decode']:
 jobs.append((f'NBH_K{len(jobs)+6:03}','format::NBH_format::NBH_'+name+'_gate'))
assert len({a for a,h in jobs})==len(jobs),jobs
(E/'NBH_BATCH1_JOBS.json').write_text(json.dumps(jobs,indent=2)+'\n')
for a,h in jobs:
 assert not (E/a/'receipt.json').exists(),a
 r=subprocess.run(['python3',str(E/'NBH_native.py'),'run',a,'pool_v1::'+h])
 if r.returncode:sys.exit(r.returncode)
