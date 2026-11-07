from NLQ_native import native,E
import lzma
jobs=[(38,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_frame',1),(39,'r1_pool_adapter::owned::NLQ_owned::guard_owned_count',0),(40,'r1_pool_adapter::owned::NLQ_owned::guard_owned_count_control',1)]
for n,target,wanted in jobs:
 a=f'NLQ_K{n:03d}';r=native(a,target)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'CBMC timed out' not in log,'STOP timed-out item; retain exact obligation'
 assert r['exit_status']==wanted,(a,'unexpected verdict')
 print(a+': expected verdict recorded',flush=True)
