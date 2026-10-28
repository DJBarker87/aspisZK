from pathlib import Path
import time,subprocess,sys,json
E=Path('evidence/pv-rdb2c-20261028');p=E/'lean-60519/receipt.json'
while not p.exists():time.sleep(5)
assert json.loads(p.read_text())['exit']==0
sys.exit(subprocess.run([sys.executable,'tools/pv-rdb2c-20261028/queue.py','weights-owned.json','60520']).returncode)
