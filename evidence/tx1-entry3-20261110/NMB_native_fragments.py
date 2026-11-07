"""Loop-free source-fragment contracts, serial paired controls; no row promotion."""
from NMB_native import *
plan=[(21,'NMB_guard_fragment_contract'),(23,'NMB_snapshot0_args_contract'),(25,'NMB_snapshot1_args_contract'),(27,'NMB_snapshot2_args_contract')]
for num,target in plan:
 for offset,invert in [(0,False),(1,True)]:
  a=f'NMB_K{num+offset:03d}';r=native(a,invert,target)
  log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  semantic=('VERIFICATION:- SUCCESSFUL'in log and r['exit_status']==0)if not invert else('VERIFICATION:- FAILED'in log and r['exit_status']==1 and 'Failed Checks:'in log and not any(t in log for t in ['CBMC timed out','unwinding failures','could not compile']))
  with(E/'NMB_FRAGMENT_VERDICTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,target=target,invert=invert,expected_semantic_verdict=semantic,whole_parent_credit=False))+'\n')
  if not semantic:raise RuntimeError('STOP fragment pair: '+a)
