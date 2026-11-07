from pathlib import Path
import json
p=Path(__file__).resolve().parent
rows=[json.loads(f.read_text())for f in p.glob('NLR_[LK][0-9][0-9][0-9]/receipt.json')]
x={}
for k in ['lean','kani','setup']:
 a=[r for r in rows if r['kind']==k];x[k]=dict(scopes=len(a),exit0=sum(r['exit_status']==0 for r in a))
print(json.dumps(x))
