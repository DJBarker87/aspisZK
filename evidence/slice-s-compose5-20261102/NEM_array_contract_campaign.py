from pathlib import Path
import sys,subprocess,re
E=Path(__file__).resolve().parent
plan=[(89,'support','support',True),(90,'real','shape_control',True),(91,'unimplied','shape_control',False),(92,'inverted','support',False),(93,'frame','support',False),(94,'oracle_support','support',True),(95,'oracle_inverted','support',False),(96,'caller','full_mutation_caller',True),(97,'wrong_window','full_mutation_caller',False),(98,'inside_unimplied','full_mutation_caller',False)]
for n,mode,harness,positive in plan:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_array_contract.py'),mode],check=True);(E/(a+'-array-contract.json')).write_bytes((E/'NEM_ARRAY_CONTRACT_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::pair_tree_profile::NEM_slice_contract::'+harness],capture_output=True,text=True);print(a,mode,r.stdout[-1300:],r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==positive and ('Failed Checks:' in t)==(not positive)
