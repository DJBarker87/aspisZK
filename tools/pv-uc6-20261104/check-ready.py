"""Read-only hash preflight: execute only the runner's binary assertion AST.
Never imports the runner, invokes a client, creates a scope, or samples timing.
"""
from pathlib import Path
import ast, hashlib, json
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
CONTROL=H.parent/'codex-pv-c474-20261029'
tree=ast.parse((H/'timing-window.py').read_text())
selected=[]
for n in tree.body:
    if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id in ['B','expected'] for x in n.targets):
        selected.append(n)
    elif isinstance(n,ast.Assert) and any(isinstance(x,ast.Name) and x.id in ['hashlib','expected'] for x in ast.walk(n.test)):
        selected.append(n)
assert len(selected)==5, 'runner preflight shape changed; review before executing'
ns=dict(H=H,CONTROL=CONTROL,hashlib=hashlib,json=json)
exec(compile(ast.Module(body=selected,type_ignores=[]),'<binary assertions only>','exec'),ns)
print(json.dumps(dict(passed=True,assertions=3,binaries={k:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for k,p in ns['B'].items()},ready_packet_sha256=hashlib.sha256((H/'final-gates/ready/build.json').read_bytes()).hexdigest(),runner_sha256=hashlib.sha256((H/'timing-window.py').read_bytes()).hexdigest(),clients_executed=0,timing_samples=0,scopes_launched=0),indent=2))
