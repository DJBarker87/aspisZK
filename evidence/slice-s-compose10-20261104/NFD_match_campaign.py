"""New exhaustive-Result observation, after isolated K077 passed unchanged caps."""
from pathlib import Path
import sys,subprocess,json
E=Path(__file__).resolve().parent
jobs=[(84,'guard',['joined','negative'],'NFD_GUARD_CURRENT.json','r1_pool_adapter::NFD_guard::guard_cut'),(85,'reconstruct',['prefix_match','positive','0'],'NFD_RECONSTRUCT_CURRENT.json','r1_pool_adapter::NFD_reconstruct::reconstruction_slice'),(86,'reconstruct',['prefix_match','negative','0'],'NFD_RECONSTRUCT_CURRENT.json','r1_pool_adapter::NFD_reconstruct::reconstruction_slice'),(87,'emit',['positive'],'NFD_EMIT_CURRENT.json','r1_pool_adapter::NFD_emit_continuation::emit_continuation'),(88,'emit',['byte'],'NFD_EMIT_CURRENT.json','r1_pool_adapter::NFD_emit_continuation::emit_continuation'),(89,'emit',['order'],'NFD_EMIT_CURRENT.json','r1_pool_adapter::NFD_emit_continuation::emit_continuation'),(90,'emit',['argument'],'NFD_EMIT_CURRENT.json','r1_pool_adapter::NFD_emit_continuation::emit_continuation')]
for n,g,args,current,h in jobs:
 a=f'NFD_K{n:03}';subprocess.run([sys.executable,str(E/('NFD_prepare_'+g+'.py')),*args],check=True)
 (E/(a+'-shape.json')).write_bytes((E/current).read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_program_kani_run.py'),a,'kani',h])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text();positive=n in [85,87];print(json.dumps(dict(attempt=a,kind=g,exit=r['exit_status'])),flush=True)
 if r['exit_status'] in [124,137] or 'timed out' in log.lower():raise SystemExit('family stopped for review; no later controls submitted')
 assert r['exit_status']==(0 if positive else 1)
 assert positive or 'Failed Checks:' in log
