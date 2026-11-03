from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode,harness in [(68,'positive','result_prefix'),(69,'wrong_reply','result_prefix'),(70,'wrong_record','result_prefix'),(71,'wrong_zero','result_prefix'),(72,'return','result_return'),(73,'return_negative','result_return'),(74,'geometry','result_geometry'),(75,'geometry_negative','result_geometry')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_result_prefix.py'),mode],check=True)
 (E/(a+'-result-prefix.json')).write_bytes((E/'NEQ_RESULT_PREFIX_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_kani_run.py'),a,'kani','pool_v1::pair_forest_terminal::NEQ_result_prefix::'+harness],capture_output=True,text=True);print(a,mode,r.stdout[-1100:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();success=mode in ['positive','return','geometry'];assert ('VERIFICATION:- SUCCESSFUL' in t)==success;assert success or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
