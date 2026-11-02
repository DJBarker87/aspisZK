from pathlib import Path
import sys,subprocess
E=Path(__file__).resolve().parent
plan=[];n=39
for case,count in [('live',8),('after',7)]:
 for slot in range(count):
  for mode in ['positive','negative']:plan.append((n,case,slot,mode));n+=1
plan += [(69,'live',7,'wrong_place'),(70,'after',6,'wrong_place')]
for n,case,slot,mode in plan:
 a=f'NEM_K{n:03}';subprocess.run([sys.executable,str(E/'NEM_prepare_encoder_window.py'),case,str(slot),mode],check=True);(E/(a+'-encoder-window.json')).write_bytes((E/'NEM_ENCODER_WINDOW_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEM_kani_run.py'),a,'kani','pool_v1::'+('pair_tree_profile' if case=='live' else 'pair_terminal')+'::NEM_encoder_window::encoder_window'],capture_output=True,text=True);print(a,case,slot,mode,r.stdout[-1300:],r.stderr,flush=True)
 assert (E/a/'receipt.json').exists();t=(E/a/'stdout.log').read_text();assert 'timed out' not in t.lower();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive') and ('Failed Checks:' in t)==(mode!='positive')
