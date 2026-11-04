"""One prepared shape, immutable per-attempt snapshot, stop on missing verdict."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);shape=sys.argv[2];extra=sys.argv[3:]
choices={'equality':('NEU_prepare_equality_step.py','NEU_EQUALITY_STEP_CURRENT.json','NEU_program_kani_run.py','r1_pool_adapter::NEU_equality_step::equality_step'),'guard':('NEU_prepare_guard_view.py','NEU_GUARD_VIEW_CURRENT.json','NEU_program_kani_run.py','r1_pool_adapter::NEU_reconstruct::reconstruction_slice'),'decode':('NEU_prepare_box_decode.py','NEU_BOX_DECODE_CURRENT.json','NEU_kani_run.py','pool_v1::pair_forest_terminal::NEU_box_decode::box_decode_window')}
p,metadata,runner,harness=choices[shape]
for mode in ['positive','negative']:
 a=f'NEU_K{n:03}';n+=1;assert n<=131
 subprocess.run([sys.executable,str(E/p),*extra,mode],check=True)
 (E/(a+'-shape.json')).write_bytes((E/metadata).read_bytes())
 r=subprocess.run([sys.executable,str(E/runner),a,'kani',harness],capture_output=True,text=True)
 print(a,shape,mode,r.stdout[-1500:],r.stderr,flush=True)
 receipt=E/a/'receipt.json'
 if not receipt.exists():raise SystemExit('STOP missing receipt, do not resubmit')
 data=json.loads(receipt.read_text());t=(E/a/'stdout.log').read_text()
 if data['exit_status']==124 or 'timed out' in t.lower():raise SystemExit('EXCLUDED timeout; isolate a new shape before further work')
 if ('VERIFICATION:- SUCCESSFUL' in t)!=(mode=='positive') or (mode=='negative' and 'Failed Checks:' not in t):raise SystemExit('STOP requires inspection')
