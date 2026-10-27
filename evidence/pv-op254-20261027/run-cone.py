from pathlib import Path
import json,subprocess,sys
H=Path('/home/dombarker/project-offloads/codex-pv-op254-20261027')
success=set()
for f in (H/'lean-receipts').glob('*/receipt.json'):
 r=json.loads(f.read_text())
 if r['charged'] and r['exit']==0:success.add(r['module'])
a=int(sys.argv[1])
for m in json.loads((H/'compile-order.json').read_text()):
 if m in success:continue
 assert 38500<=a<=38596
 p=subprocess.run(['python3',str(H/'lean.py'),str(a),m])
 if p.returncode:sys.exit(p.returncode)
 a+=1
print('next_unused='+str(a))
