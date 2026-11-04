from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(31,'length',['positive'],'NFD_LENGTH_CURRENT.json','pool_v1::pair_forest_terminal::NFD_length::length_gate'),(32,'length',['value'],'NFD_LENGTH_CURRENT.json','pool_v1::pair_forest_terminal::NFD_length::length_gate'),(33,'request',['0','argument'],'NFD_REQUEST_CURRENT.json','pool_v1::pair_forest_terminal::NFD_request::request'),(34,'request',['11','value'],'NFD_REQUEST_CURRENT.json','pool_v1::pair_forest_terminal::NFD_request::request')]
for n,g,args,shape,h in jobs:
 a=f'NFD_K{n:03}';subprocess.run([sys.executable,str(E/('NFD_prepare_'+g+'.py')),*args],check=True)
 (E/(a+'-shape.json')).write_bytes((E/shape).read_bytes())
 subprocess.run([sys.executable,str(E/'NFD_kani_run.py'),a,'kani',h])
 r=json.loads((E/a/'receipt.json').read_text());log=(E/a/'stdout.log').read_text()
 if 'timed out' in log.lower() or r['exit_status'] in [124,137]:raise SystemExit('family stopped for timeout review')
 assert r['exit_status']==(0 if n==31 else 1)
 assert n==31 or 'Failed Checks:' in log
