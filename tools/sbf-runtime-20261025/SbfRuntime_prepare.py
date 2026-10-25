"""Local data preparation only; never imports or executes backend definitions."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).parent
OUT = HERE.parent.parent/'evidence/sbf-runtime-20261025'
def pin(raw):
    return dict(size=len(raw), sha256=hashlib.sha256(raw).hexdigest())

def expr(node, values):
    if isinstance(node, ast.Constant): return node.value
    if isinstance(node, ast.Name): return values[node.id]
    if isinstance(node, ast.Tuple): return tuple(expr(x, values) for x in node.elts)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return expr(node.left,values)+expr(node.right,values)
    if isinstance(node, ast.Subscript):
        if isinstance(node.slice, ast.Slice):
            s=node.slice
            return expr(node.value,values)[slice(expr(s.lower,values) if s.lower else None,expr(s.upper,values) if s.upper else None,None)]
        return expr(node.value,values)[expr(node.slice,values)]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub): return -expr(node.operand,values)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr=='replace':
        return expr(node.func.value,values).replace(*(expr(x,values) for x in node.args))
    raise ValueError(ast.dump(node))

values={}
imports={}
for label in ('capture','abi','backend','entry'):
    raw=(HERE/f'SbfRuntime-{label}.py.txt').read_bytes()
    tree=ast.parse(raw)
    imports[label]=sorted({n.names[0].name if isinstance(n,ast.Import) else n.module for n in ast.walk(tree) if isinstance(n,(ast.Import,ast.ImportFrom))})
    for n in tree.body:
        if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('FD_AUDIT_TEXT','PROBE_TEXT','PROBE','POSTEXEC','FIXED_PROBE','ENV','ROOT'):
            name=n.targets[0].id
            if name in ('ENV','ROOT'): values[name]=ast.literal_eval(n.value) if name=='ENV' else '/var/lib/SbfSeal-20261025-v1/rootfs'
            else: values[name]=expr(n.value,values)
required=sorted({x for xs in imports.values() for x in xs if not x.startswith('SbfLinux')})
# ast.Import may have multiple names: retain all, including fixed probe imports.
for label in ('capture','abi','backend'):
    for n in ast.walk(ast.parse((HERE/f'SbfRuntime-{label}.py.txt').read_text())):
        if isinstance(n,ast.Import): required=sorted(set(required)|{a.name for a in n.names})
probe_imports=sorted({a.name for n in ast.walk(ast.parse(values['FIXED_PROBE'][-1])) if isinstance(n,ast.Import) for a in n.names})
required=sorted(set(required)|set(probe_imports))
sourcepins={p.name:pin(p.read_bytes()) for p in sorted(HERE.glob('SbfRuntime-*.py.txt'))}
historical=json.loads((OUT/'SbfRuntime-historical-runtime.json').read_text())
data=dict(historical_runtime={k:historical[k] for k in ('revision','executable','executable_pin','version')},source_revision='9f50be799e',guard_revision='13abf7fe51',sources=sourcepins,imports=imports,required_modules=required,probe_imports=probe_imports,fixed_probe=list(values['FIXED_PROBE']),env=values['ENV'],root=values['ROOT'])
(OUT/'SbfRuntime-source-inputs.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
guard=(HERE/'SbfRuntime-guard.py.txt').read_text()
body=(HERE/'SbfRuntime_acquire_body.py.txt').read_text()
payload='# SbfRuntime fixed metadata payload; original guard follows verbatim.\n'+guard+'\n# End verbatim guard.\n'+body.replace('SBF_RUNTIME_INPUTS = None','SBF_RUNTIME_INPUTS = '+repr(data))
(HERE/'SbfRuntime_payload.py.txt').write_text(payload)
print(json.dumps(dict(payload=pin(payload.encode()),sources=sourcepins,required=required),sort_keys=True))
