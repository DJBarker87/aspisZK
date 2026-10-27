from pathlib import Path
import json,re,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-extract-20261027');rs=json.loads((D/'inventory-llbc.json').read_text());seen=set()
for i,r in enumerate(rs):
 op=re.search(r'op(\d+)',r['evidence'])
 if not op:continue
 op=int(op[1])
 if op in seen or op==223:continue
 seen.add(op); out=D/f'op{op}-diagnostic-generated';ns=f'PV_Ext_DiagnosticOp{op}'
 args=['timeout','120',str(D/'pipeline/base/src/_build/default/main.exe'),'-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',ns,'-dest',str(out),'-split-files','-emit-json',r['own_llbc']]
 p=subprocess.run(['python3',str(D/'run_host.py'),f'aeneas-op{op}-diagnostic-001',json.dumps(args)])
 if p.returncode:break
 receipt=json.loads((D/f'aeneas-op{op}-diagnostic-001/receipt.json').read_text()); print(op,receipt['exit'],flush=True)
 if receipt['exit']==78:break
