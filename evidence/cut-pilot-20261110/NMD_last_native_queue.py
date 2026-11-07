from NMD_native import *
(E/'NMD_native.rs').write_text((E/'NMD_generic_record.rs').read_text())
for i,name in enumerate(['NMD_record_local_channel','NMD_record_local_channel_mutant','NMD_copy_control'],120):
 a=f'NMD_K{i:03}';r=native(a,'verifier::candidate::NMD_native::'+name)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();assert 'could not compile' not in log and 'Traceback' not in log
 if 'timed out' in log.lower():raise RuntimeError('Retire generic local-channel shape')
from NMD_program import native as program
(E/'NMD_program.rs').write_text((E/'NMD_program_route_b.rs').read_text())
for i,name in enumerate(['NMD_program_contract','NMD_program_inverse','NMD_program_real','NMD_program_cut','NMD_program_bad_reply','NMD_program_bad_state','NMD_copy_control'],123):
 a=f'NMD_K{i:03}';r=program(a,'r1_pool_adapter::owned::NMD_program::'+name)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();assert 'could not compile' not in log and 'Traceback' not in log
 if 'timed out' in log.lower():raise RuntimeError('Retire ProgramResult local-record shape')
