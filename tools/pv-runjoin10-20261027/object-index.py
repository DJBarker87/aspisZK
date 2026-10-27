#!/usr/bin/env python3
"""Hash retained own proof objects without launching a scope or compiler."""
import json,pathlib,shlex,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin10-20261027'
rows=[json.loads(p.read_text()) for p in e.glob('receipt-*.json')]
modules=sorted({r['target'] for r in rows if r['accepted']})
job='/home/dombarker/project-offloads/codex-pv-runjoin-20261026'
code='''import pathlib,hashlib,json
root=pathlib.Path(%r);rows=[]
for module in %r:
 p=root/(module+'.olean')
 rows.append(dict(module=module,path=str(p),exists=p.is_file(),sha256=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,size=p.stat().st_size if p.is_file() else None))
print(json.dumps(rows))
'''%(job+'/lean-objects',modules)
r=subprocess.run(['ssh','-o','BatchMode=yes','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True)
x=json.loads(r.stdout);assert all(p['exists'] for p in x)
(e/'own-object-index.json').write_text(json.dumps(x,indent=2)+'\n')
original={r['module'].replace('.','/') for r in json.loads((e/'original25-plan.json').read_text())}
assert original <= {r['module'] for r in x}
(e/'original25-restored.json').write_text(json.dumps(dict(before=25,after=0,all_retained=True,modules=[p for p in x if p['module'] in original]),indent=2)+'\n')
print(len(x),'own objects retained and hashed; original 25→0')
