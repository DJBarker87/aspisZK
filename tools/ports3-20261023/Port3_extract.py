#!/usr/bin/env python3
"""Current source stage children: capped extraction, isolated outputs/cache."""
from pathlib import Path
import json,subprocess,shlex,sys
R=Path(__file__).resolve().parents[2];T=R/'tools/ports3-20261023';E=R/'evidence/ports3-20261023'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-ports3-20261023'
kind=sys.argv[1];n=1+max((int(p.stem.split('-')[1]) for p in T.glob(kind+'-*.json')),default=0);a=f'{kind}-{n:03d}'
if kind=='charon':
 old=json.loads((R/'tools/verifier-top-20261023/charon-002.json').read_text())
 c=old['command'];idx=c.index('--include');end=c.index('--consts')
 layouts=c[idx:end]; kept=[]
 for i in range(0,len(layouts)):
  if layouts[i]=='--include' and 'candidate::tx' not in layouts[i+1]:kept+=layouts[i:i+2]
 roots=['crate::verifier::candidate::'+n for n in ['tx1','tx2_common','tx2_authenticated','batch_merkle','batch_merkle_values','batch_tree','query_loop','query_values']]
 roots+=['crate::verifier::'+n for n in ['resume','finish_relation','accumulate_batched_with_node']]
 roots+=['crate::verifier::{crate::verifier::'+ty+'}::'+fn for ty,fn in [('Accumulator','new'),('BatchedWeights','new'),('BatchedWeights','finish'),('QueryGeometry','for_range')]]
 cmd=c[:idx]
 for root in roots:
  cmd+=['--include',root]
  if '{' not in root:cmd+=['--start-from',root]
 for layout in ['crate::multiproof::Arity','crate::verifier::Reader','aspis_core::r0::domain::FibreIndex','aspis_core::r0::domain::Point']:
  kept+=['--include',layout]
 for method in ['new','finish','for_range']:
  kept+=['--include','crate::verifier::_::'+method]
 cmd+=kept+c[end:]
 cmd=[s.replace('/home/dombarker/project-offloads/codex-cx-verifier-top-20261023',B).replace('VTop_Stages.llbc','Port3_StageChildren.llbc') for s in cmd]
 cfg={**old,'attempt':a,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'command':cmd,'sources':old['sources'],'timeout':300,
 'deps_fingerprint':{'scope':'Current unchanged shipped source snapshot, P6 pins in kani001; only twelve requested child roots transparent; all other library/backend/callee bodies opaque'},
 'expected_time':'Optimized Rust compilation and MIR extraction of twelve stage child roots; no field elimination or Lean build'}
 cfg['env']['CARGO_TARGET_DIR']=B+'/charon-target'
else:
 old=json.loads((R/'tools/verifier-top-20261023/aeneas-002.json').read_text())
 cmd=[s.replace('/home/dombarker/project-offloads/codex-cx-verifier-top-20261023',B).replace('VTop_Stages','Port3_StageChildren') for s in old['command']]
 cmd.remove('-abort-on-error')
 cmd+=['-diagnose-translation']
 cfg={**old,'attempt':a,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'command':cmd,'sources':['Port3_StageChildren.llbc'],'timeout':180,
 'deps_fingerprint':{'scope':'charon001 current source body extraction; exact LLBC snapshotted'},'expected_time':'Aeneas symbolic translation of current child bodies, no Lean replay or arithmetic aggregation'}
(T/f'{a}.json').write_text(json.dumps(cfg,indent=2)+'\n')
admission=(T/'Port3_kani.py').read_text().split("admission='''",1)[1].split("'''",1)[0]
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(admission)],capture_output=True,text=True,check=True);(E/f'{a}-reservation.json').write_text(r.stdout)
subprocess.run(['scp','-q',str(T/f'{a}.json'),str(T/'Port3_run_host.py'),H+':'+B+'/'],check=True)
r=subprocess.run(['ssh',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port3_run_host.py {a}.json'],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(E)],check=True)
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
