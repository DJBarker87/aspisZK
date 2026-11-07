"""Independent negative controls; retire a timeout and proceed to next mutant."""
from NMM_bl_lane import *
import sys
start=int(sys.argv[1]);jobs=[(branch,mode) for branch in ['success_meta_ptr','success_root_ptr','success_frontier_ptr'] for mode in ['reply','argument','footprint','copy']]
for i,(branch,mode) in enumerate(jobs):
 a='NMM_K'+str(start+i).zfill(3);r=attempt(a,branch,mode)
 out=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 timed='cbmc timed out' in out.lower()
 failed='VERIFICATION:- FAILED' in out and r['exit_status']==1 and not timed
 status='EXPECTED_FAILURE' if failed else 'TIMEOUT_RETIRED_NO_CREDIT' if timed else 'UNEXPECTED_STOP'
 with (E/'NMM_CONTROL_VERDICTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,branch=branch,mode=mode,status=status,exit_status=r['exit_status']))+'\n')
 assert failed or timed, 'Inspect unexpected result before any next launch: '+a
