"""Pre-host source inspection only; no old suite or payload execution."""
import ast
import hashlib
import json
from pathlib import Path
import resource
import sys
import time
START=time.monotonic()
HERE=Path(__file__).resolve().parent
OUT=HERE.parents[1]/'evidence/sbf-runtime-trace-20261025'
def pin(raw): return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
guard=(HERE/'SbfRuntimeTrace-guard.py.txt').read_bytes()
payload=(HERE/'SbfRuntimeTrace_payload.py.txt').read_bytes()
checks=[]
def check(name,ok):
    checks.append(dict(name=name,passed=bool(ok)))
    if not ok: raise ValueError(name)
check('exact authorized guard',pin(guard)==dict(size=8426,sha256='9f0fbfd713895348a3df87fb4bb8643a85a4facb1d5ce95e31ad7839db74ca6d'))
check('guard unchanged prefix exactly once',payload.startswith(guard) and payload.count(guard)==1)
tree=ast.parse(payload)
guardtree=ast.parse(guard)
check('all guard AST prefix unchanged',ast.dump(ast.Module(body=tree.body[:len(guardtree.body)],type_ignores=[]))==ast.dump(guardtree))
protected={'BUDGET','INTERVAL','MAX_SAMPLES','MAX_LINEAGE','Guard','GuardError','Proc','inherited_limits','check_limits'}
later=ast.Module(body=tree.body[len(guardtree.body):],type_ignores=[])
check('no protected definitions replaced',not any(isinstance(n,(ast.FunctionDef,ast.ClassDef)) and n.name in protected or isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store) and n.id in protected for n in ast.walk(later)))
check('no resource setters',not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr in ('setrlimit','prlimit') for n in ast.walk(tree)))
calls=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='Popen']
check('exactly one executable launch site',len(calls)==1)
tracee=(HERE/'SbfRuntimeTrace-tracee.py.txt').read_bytes()
tt=ast.parse(tracee)
imports=sorted({a.name for n in ast.walk(tt) if isinstance(n,ast.Import) for a in n.names})
inputs=json.loads((OUT/'SbfRuntimeTrace-sourcepins.json').read_text())
check('fixed ordinary imports only',imports==sorted(set(inputs['required_modules'])|{'sys'}))
check('no backend/probe body in tracee',b'SbfLinux' not in tracee and b'ctypes.CDLL' not in tracee and b'ctypes.PyDLL' not in tracee)
check('new fixtures passed',json.loads((OUT/'SbfRuntimeTrace-fixtures-receipt.json').read_text())['exit']==0)
receipt=dict(target='pre-host changed source review',exit=0,checks=checks,
    argv=getattr(sys,'orig_argv',sys.argv),argv_source='sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv',
    source_revision=(OUT/'SbfRuntimeTrace-entry.txt').read_text().strip(),wall_seconds=time.monotonic()-START,
    peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024),
    swap_operations=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,axioms='N/A',
    sourcepins={p.name:pin(p.read_bytes()) for p in HERE.iterdir() if p.is_file()},
    dependencies={n:dict(file=getattr(m,'__file__',None),pin=pin(Path(m.__file__).read_bytes()) if getattr(m,'__file__',None) and Path(m.__file__).is_file() else None) for n,m in sorted(sys.modules.items()) if m is not None})
(OUT/'SbfRuntimeTrace-review-receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print(json.dumps(dict(exit=0,checks=len(checks))))
