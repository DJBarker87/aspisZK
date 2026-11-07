from NMB_native import *
for a,mode in [('NMB_K031',True),('NMB_K032','frame')]:
 r=native(a,mode,'NMB_array_header_contract')
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 valid=r['exit_status']==1 and 'VERIFICATION:- FAILED'in log and 'Failed Checks:'in log and not any(s in log for s in ['CBMC timed out','unwinding failures','could not compile'])
 with(E/'NMB_HEADER_CONTROLS.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,mode=mode,expected_failing_verdict=valid,review_required=True))+'\n')
 if not valid:raise RuntimeError('STOP header frame control '+a)
