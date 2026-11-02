from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
for n,mode in [(99,'positive'),(100,'wrong_after'),(101,'wrong_byte')]:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_late_tail.py'),mode],check=True);(E/(a+'-late-tail.json')).write_bytes((E/'NEM_LATE_TAIL_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::pair_tree_profile::NEM_slice_contract::tail_control'],capture_output=True,text=True);print(a,mode,r.stdout[-1500:],r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode!='positive')
