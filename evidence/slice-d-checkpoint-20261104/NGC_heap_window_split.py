from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
s=s.replace('Layout::array::<T>(32769)','Layout::array::<T>(2)').replace('Vec::from_raw_parts(ptr,len,32769)','Vec::from_raw_parts(ptr,len,2)')
s=s.replace('kani::assume(prefix<=32768&&j<=prefix)','kani::assume(prefix<=1&&j<=prefix)')
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
(E/'NGC_HEAP_WINDOW_SPLIT.json').write_text(json.dumps(dict(excluded=['NGC_K066 full32769 resize prestate','NGC_K096 full32769 push prestate','NGC_K097 mistakenly submitted control; excluded'],replacement='Original resize_step_* harness names, physical two-element window: prefix0or1, observe old cell or written cell, full one-step native std resize with spare capacity. Generic logical offset/frame and full resize interpretation remain separate Lean/Std obligations; this probe alone is not arbitrary32768 resize.',no_global_claim_from_narrow_window=True),indent=1)+'\n')
s='from pathlib import Path\nimport subprocess,os,json\nE=Path(__file__).resolve().parent\n'
for typ,ps in zip(['u8','q','raw','wide'],[(99,100),(31,32),(33,34),(35,67)]):
 for k,inv in zip(ps,[False,True]):
  s+="env=os.environ.copy();env.pop('NGC_INVERT',None)\n"+("env['NGC_INVERT']='1'\n" if inv else '')+f"r=subprocess.run(['python3',str(E/'NGC_run.py'),'NGC_K{k:03}','kani','verifier::NGC_windows::resize_step_{typ}'],env=env,capture_output=True,text=True);(E/'NGC_K{k:03}-local.log').write_text(r.stdout+r.stderr);print('NGC_K{k:03}',r.returncode,flush=True)\n"
  s+=f"log=(E/'NGC_K{k:03}/stdout.log').read_text()\nif 'timed out' in log or r.returncode!={1 if inv else 0}:raise SystemExit('Stop family on timeout/unexpected verdict')\n"
(E/'NGC_queue_window.py').write_text(s)
