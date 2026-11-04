from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for n,shape,mode in [(37,'common','negative'),(38,'common_actual','positive')]:
 a=f'NFD_K{n:03}';subprocess.run([sys.executable,str(E/'NFD_prepare_reconstruct.py'),shape,mode,'0'],check=True)
 (E/(a+'-shape.json')).write_bytes((E/'NFD_RECONSTRUCT_CURRENT.json').read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani','r1_pool_adapter::NFD_reconstruct::reconstruction_slice'])
 rc=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if rc['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped: timeout review required')
 assert rc['exit_status']==(0 if mode=='positive' else 1)
 assert mode=='positive' or 'Failed Checks:' in log
