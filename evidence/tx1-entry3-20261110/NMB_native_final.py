from NMB_native import *
for start,target in [(35,'NMB_owned_select_contract'),(37,'NMB_checked_span_contract'),(39,'NMB_dispatch_fragment_contract')]:
 for delta,invert in [(0,False),(1,True)]:
  a=f'NMB_K{start+delta:03d}';r=native(a,invert,target)
  log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  valid=('VERIFICATION:- SUCCESSFUL'in log and r['exit_status']==0)if not invert else('VERIFICATION:- FAILED'in log and r['exit_status']==1 and 'Failed Checks:'in log and not any(s in log for s in ['CBMC timed out','unwinding failures','could not compile']))
  with(E/'NMB_FRAGMENT_VERDICTS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,target=target,invert=invert,expected_semantic_verdict=valid,whole_parent_credit=False))+'\n')
  if not valid:raise RuntimeError('STOP fragment: '+a)
