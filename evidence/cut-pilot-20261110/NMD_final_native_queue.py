from NMD_native import *
import subprocess
subprocess.run([sys.executable,str(E/'NMD_guard_queue.py'),'101'],check=True)
(E/'NMD_native.rs').write_text((E/'NMD_generic_record.rs').read_text())
for i,name in enumerate(['NMD_record_contract','NMD_record_inverse','NMD_record_weak_contract','NMD_record_weak_inverse','NMD_record_modifies','NMD_record_real','NMD_record_unimplied','NMD_record_parent','NMD_record_parent_mutant','NMD_copy_control'],111):
 a=f'NMD_K{i:03}';r=native(a,'verifier::candidate::NMD_native::'+name)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 with (E/'NMD_GENERIC_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,target=name,exit=r['exit_status'],timeout='timed out' in log.lower(),compile_error='could not compile' in log))+'\n')
 assert 'Traceback' not in log and 'Failed to match' not in log
 if 'timed out' in log.lower():raise RuntimeError('Retire original-length generic-record shape; do not launch its unchanged siblings')
 if 'could not compile' in log and name!='NMD_record_parent':raise RuntimeError('Own source compile error; stop before another launch')
