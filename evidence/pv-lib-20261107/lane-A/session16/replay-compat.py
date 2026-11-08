import json,subprocess,pathlib,sys
E=pathlib.Path(__file__).parent
plan=json.loads((E/'COMPAT_PLAN.json').read_text())
ids=[55688,55689]+list(range(55900,55931))
for a,m in zip(ids,plan['order']):
 module=plan['mapping'][m];src='lean/'+module+'.lean'
 subprocess.run(['git','add',src,str(E)],check=True)
 r=subprocess.run(['python3',str(E/'compile.py'),str(a),module])
 if r.returncode:sys.exit(r.returncode)
 subprocess.run(['git','add',str(E)],check=True)
 subprocess.run(['git','commit','--only',src,str(E),'-m','proof: replay '+m+' in pinned C18 compatibility cohort'],check=True)
