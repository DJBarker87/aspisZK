#!/usr/bin/env python3
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'docs/research/100bit-spend-path-20261013/evidence/port-integrate-20261021'
p=json.loads((E/'plan.json').read_text()); failed=[]; blocked=[]
import re
for m in p['compile_order']:
 s=R/'docs/research/100bit-spend-path-20261013/lean'/(m+'.lean')
 deps=re.findall(r'^import\s+(\S+)',s.read_text(),re.M)
 if any(d in failed+blocked for d in deps):
  blocked.append(m);print('BLOCKED',m,flush=True);continue
 result=subprocess.run([sys.executable,str(R/'tools/port-integrate/compile.py'),m],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/'driver.log').open('a').write(result.stdout+'\n')
 print(m,'PASS' if result.returncode==0 else 'FAIL',flush=True)
 if result.returncode:failed.append(m);print(result.stdout[-1800:],flush=True)
(E/'run-status.json').write_text(json.dumps(dict(failed=failed,blocked=blocked),indent=2)+'\n')
sys.exit(bool(failed or blocked))
