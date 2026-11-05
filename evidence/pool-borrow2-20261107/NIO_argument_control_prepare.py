"""Additional argument-association control for the passing K103 configuration."""
from pathlib import Path
import sys,json,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
r=subprocess.run([sys.executable,str(E/'NIO_fixed_loop_prepare.py'),'0','positive'],capture_output=True,text=True);assert r.returncode==0
sys.path.insert(0,str(E));from NIO_native_prepare import stage
p=E/'NIO_CURRENT.json';x=json.loads(p.read_text());old='NIO_step(&mut lane_data,&a0)?;';new='NIO_step(&mut lane_data,&a1)?;';assert x['source'].count(old)==1
source=x['source'].replace(old,new)
stage('programs/aspis-pool/src/pair_forest.rs',source,'additional wrong-account argument control for K103','negative',x['domain'],'Control only, not production reachability or a passing caller certificate.',dict(member='process_pair_forest_initialize_with_runtime_v1',expected_verdict='FAIL',matched_positive='NIO_K103',first_control='NIO_K104',source_corruption='Pass the already-held master cell instead of the new lane cell; original one-iteration body unchanged.'))
print('Additional argument control for passing K103 prepared')
