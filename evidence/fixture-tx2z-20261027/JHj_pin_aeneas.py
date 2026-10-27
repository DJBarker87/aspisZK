from pathlib import Path
import json,subprocess,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
pins=json.loads((R/'evidence/fixture-tx2y-20261027/JHi_AENEAS_OBJECT_PINS.json').read_text())
code='''import json,sys,hashlib\nfrom pathlib import Path\nrows=json.load(sys.stdin)\nfor row in rows:\n p=Path(row['path']);row['actual_sha256']=hashlib.sha256(p.read_bytes()).hexdigest();row['actual_bytes']=p.stat().st_size\nprint(json.dumps(rows,indent=2))'''
import shlex
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(pins),text=True,capture_output=True)
r.check_returncode();rows=json.loads(r.stdout)
assert all(x['sha256']==x['actual_sha256'] and x['bytes']==x['actual_bytes'] for x in rows)
(P/'JHj_AENEAS_OBJECT_PINS.json').write_text(r.stdout)
print(len(rows),'inherited resolved Aeneas objects unchanged')
