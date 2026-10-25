"""Immutable-source extraction and payload assembly only; no backend execution."""
import ast
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
OUT=ROOT/'evidence/sbf-runtime-trace-20261025'
def blob(rev,path): return subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT)
def pin(raw): return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
sources={}
for label in ('abi','backend','capture','entry'):
    path='tools/sbf-linux-20261025/SbfLinux_'+label+'.py'
    raw=blob('9f50be799e',path)
    (HERE/('SbfRuntimeTrace-'+label+'.py.txt')).write_bytes(raw)
    sources[label]=dict(revision='9f50be799e',path=path,**pin(raw))
guard=blob('13abf7fe51','tools/resource-meta1g-20261025/ResourceMeta1G_guard.py')
(HERE/'SbfRuntimeTrace-guard.py.txt').write_bytes(guard)
assert pin(guard)['sha256']=='9f0fbfd713895348a3df87fb4bb8643a85a4facb1d5ce95e31ad7839db74ca6d'
inputs=json.loads(blob('338af425c9','evidence/sbf-runtime-20261025/SbfRuntime-source-inputs.json'))
# Recheck complete AST import sets against the previously derived public inputs.
required=set()
for label in ('abi','backend','capture'):
    for n in ast.walk(ast.parse((HERE/('SbfRuntimeTrace-'+label+'.py.txt')).read_bytes())):
        if isinstance(n,ast.Import): required.update(a.name for a in n.names)
        elif isinstance(n,ast.ImportFrom): required.add(n.module)
for n in ast.walk(ast.parse(inputs['fixed_probe'][-1])):
    if isinstance(n,ast.Import): required.update(a.name for a in n.names)
required={x for x in required if not x.startswith('SbfLinux')}
assert sorted(required)==inputs['required_modules']
tracee="""import os,sys
os.write(1,('SbfRuntimeTrace_READY '+str(os.getpid())+'\\n').encode('ascii'))
if os.read(0,1)!=b'G': raise RuntimeError('missing collector release')
"""+'\n'.join('import '+x for x in sorted(required))+"""
modules={n:dict(file=getattr(m,'__file__',None),cached=getattr(m,'__cached__',None)) for n,m in sorted(list(sys.modules.items())) if m is not None}
with open('/proc/self/maps','r',encoding='ascii') as stream:
 maps=stream.read(1048577)
if len(maps)>1048576: raise RuntimeError('maps bound')
print(json.dumps(dict(pid=os.getpid(),threads=threading.active_count(),modules=modules,maps=maps,version=sys.version,argv=getattr(sys,'orig_argv',sys.argv),argv_source='sys.orig_argv' if hasattr(sys,'orig_argv') else 'sys.argv'),sort_keys=True))
"""
(HERE/'SbfRuntimeTrace-tracee.py.txt').write_text(tracee)
old=blob('338af425c9','tools/sbf-runtime-20261025/SbfRuntime_acquire_body.py.txt').decode()
node=next(n for n in ast.parse(old).body if isinstance(n,ast.FunctionDef) and n.name=='parse_elf')
elf=ast.get_source_segment(old,node)+'\n'
(HERE/'SbfRuntimeTrace-elf.py.txt').write_text(elf)
inputs.update(new_sourcepins=sources,guard_pin=pin(guard),source_assessment='immutable public source only; not a new identity or admission gate')
(OUT/'SbfRuntimeTrace-sourcepins.json').write_text(json.dumps(inputs,sort_keys=True,indent=2)+'\n')
fixtures=blob('338af425c9','evidence/sbf-seal-20261025/SbfSeal-trace-fixtures.json')
(OUT/'SbfRuntimeTrace-reused-fixtures.json').write_bytes(fixtures)
body=(HERE/'SbfRuntimeTrace_acquire.py.txt').read_text().replace('SBF_RUNTIME_INPUTS = None','SBF_RUNTIME_INPUTS = '+repr(inputs)).replace('TRACEE_SOURCE = None','TRACEE_SOURCE = '+repr(tracee))
payload=guard.decode()+'\n# End unchanged reviewed guard\n'+(HERE/'SbfRuntimeTrace_paths.py').read_text()+'\n'+(HERE/'SbfRuntimeTrace_parse.py').read_text()+'\n'+elf+'\n'+body
ast.parse(payload)
(HERE/'SbfRuntimeTrace_payload.py.txt').write_text(payload)
print(json.dumps(dict(payload=pin(payload.encode()),tracee=pin(tracee.encode()),required=sorted(required)),sort_keys=True))
