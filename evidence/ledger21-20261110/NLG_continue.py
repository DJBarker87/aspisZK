from pathlib import Path
import time,subprocess,sys,json
E=Path(__file__).resolve().parent
while not(E/'NLG_L008/receipt.json').exists() or(E/'NLG_CLIENT_ACTIVE').exists():time.sleep(3)
assert json.loads((E/'NLG_L008/receipt.json').read_text())['exit_status']==0
r=subprocess.run([sys.executable,str(E/'NLG_queue.py'),'raw']);sys.exit(r.returncode)
