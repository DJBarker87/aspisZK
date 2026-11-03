from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,mode in [(81,'positive'),(82,'wrong_statement'),(83,'wrong_result_place'),(84,'wrong_output'),(85,'wrong_reply')]:
 a=f'NEQ_K{n:03}';subprocess.run([sys.executable,str(E/'NEQ_prepare_emit.py'),mode],check=True)
 (E/(a+'-emit.json')).write_bytes((E/'NEQ_EMIT_CURRENT.json').read_bytes())
 r=subprocess.run([sys.executable,str(E/'NEQ_program_kani_run.py'),a,'kani','r1_pool_adapter::NEQ_emit::emit_caller'],capture_output=True,text=True);print(a,mode,r.stdout[-1200:],r.stderr,flush=True)
 t=(E/a/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' in t)==(mode=='positive');assert mode=='positive' or ('VERIFICATION:- FAILED' in t and 'Failed Checks:' in t);assert 'timed out' not in t.lower()
