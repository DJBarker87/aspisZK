from NLQ_native import native,E
import json,lzma
jobs=[(18,'r1_pool_adapter::NLQ_adapter::entry_tx1_cut_control',1),
 (19,'NLQ_native::KMX_checks::KMX_ptr_correct',0),(20,'NLQ_native::KMX_checks::KMX_ptr_wrong',1)]
for n,target,wanted in jobs:
 a=f'NLQ_K{n:03d}';r=native(a,target)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'CBMC timed out' not in log,'STOP: timeout, isolate before another run'
 assert r['exit_status']==wanted,(a,'unexpected verdict')
 print(a+': expected verdict recorded',flush=True)
