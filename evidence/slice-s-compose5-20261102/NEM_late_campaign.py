from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
plan=[(84,'late_prefix',['positive'],'NEM_late_prefix::late_prefix',True),(85,'late_prefix',['negative'],'NEM_late_prefix::late_prefix',False),(86,'slice_contract',['support'],'NEM_slice_contract::support',True),(87,'slice_contract',['real'],'NEM_slice_contract::shape_control',True),(88,'slice_contract',['unimplied'],'NEM_slice_contract::shape_control',False),(89,'slice_contract',['inverted'],'NEM_slice_contract::support',False),(90,'slice_contract',['frame'],'NEM_slice_contract::support',False),(91,'slice_contract',['oracle_support'],'NEM_slice_contract::support',True),(92,'slice_contract',['oracle_inverted'],'NEM_slice_contract::support',False),(93,'slice_contract',['caller'],'NEM_slice_contract::full_mutation_caller',True),(94,'slice_contract',['wrong_window'],'NEM_slice_contract::full_mutation_caller',False),(95,'slice_contract',['inside_unimplied'],'NEM_slice_contract::full_mutation_caller',False)]
for n,script,args,harness,positive in plan:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/('NEM_prepare_'+script+'.py')),*args],check=True)
 for p in E.glob('NEM_*CURRENT.json'):(E/(a+'-'+p.name)).write_bytes(p.read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::pair_tree_profile::'+harness],capture_output=True,text=True);print(a,args,r.stdout[-1300:],r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==positive and ('Failed Checks:' in t)==(not positive)
