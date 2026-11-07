from NMD_program import *
import subprocess
(E/'NMD_program.rs').write_text((E/'NMD_program_route_b_scalar.rs').read_text())
for i,name in enumerate(['NMD_program_contract','NMD_program_inverse','NMD_program_cut','NMD_program_bad_reply','NMD_program_bad_state','NMD_copy_control'],124):
 a=f'NMD_K{i:03}';r=native(a,'r1_pool_adapter::owned::NMD_program::'+name)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode();assert 'could not compile' not in log and 'Traceback' not in log
 if 'timed out' in log.lower():raise RuntimeError('Retire scalar ProgramResult shape; no unchanged retry')
subprocess.run([sys.executable,str(E/'NMD_final_gate_queue.py')],check=True)
