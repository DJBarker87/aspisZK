from NLQ_native import native,E
import lzma
jobs=[(23,'NLQ_native::KMX_checks::KMX_ptr_correct',0),(24,'NLQ_native::KMX_checks::KMX_ptr_wrong',1)]
jobs.append((25,'r1_pool_adapter::owned::NLQ_owned::guard_instruction',0))
jobs.append((26,'r1_pool_adapter::owned::NLQ_owned::guard_instruction_control',1))
jobs.append((27,'r1_pool_adapter::owned::NLQ_owned::guard_count',0))
jobs.append((28,'r1_pool_adapter::owned::NLQ_owned::guard_count_control',1))
jobs.append((29,'r1_pool_adapter::owned::NLQ_owned::guard_owned_instruction',0))
jobs.append((30,'r1_pool_adapter::owned::NLQ_owned::guard_owned_instruction_control',1))
jobs.append((31,'r1_pool_adapter::owned::NLQ_owned::guard_owned_count',0))
jobs.append((32,'r1_pool_adapter::owned::NLQ_owned::guard_owned_count_control',1))
jobs.append((33,'r1_pool_adapter::owned::NLQ_owned::contract_program_result',0))
jobs.append((34,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_invert',1))
jobs.append((35,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_weak',0))
jobs.append((36,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_real',0))
jobs.append((37,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_unimplied',1))
jobs.append((38,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_frame',1))
jobs.append((39,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_caller',0))
jobs.append((40,'r1_pool_adapter::owned::NLQ_owned::contract_program_result_caller_control',1))
for n,target,wanted in jobs:
 a=f'NLQ_K{n:03d}';r=native(a,target)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'CBMC timed out' not in log,'STOP: timeout, isolate instead of repeating'
 assert r['exit_status']==wanted,(a,'unexpected verdict; retain finding')
 print(a+': expected verdict recorded',flush=True)
