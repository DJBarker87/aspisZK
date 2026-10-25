"""Source/hash/AST audit only; Git reads immutable blobs, no host/native probe."""
from pathlib import Path
import ast,difflib,hashlib,json,resource,subprocess,sys,time
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
start=time.monotonic();commands=[]
def blob(rev,path):
    argv=['git','show',rev+':'+path];commands.append(argv)
    return subprocess.check_output(argv,cwd=ROOT)
def pin(raw):return dict(sha256=hashlib.sha256(raw).hexdigest(),size=len(raw))
def funcs(raw):
    source=raw.decode();tree=ast.parse(source);out={}
    def visit(nodes,prefix=''):
        for n in nodes:
            if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)):
                out[prefix+n.name]=dict(bytes=pin(ast.get_source_segment(source,n).encode()),AST=pin(ast.dump(n,include_attributes=False).encode()))
            if isinstance(n,ast.ClassDef):visit(n.body,prefix+n.name+'.')
    visit(tree.body);return out
prefix='tools/prover-rw-20261023/final-native-gate/'
identity={};diff=[]
for name in ('FinalNativeGate.py','FinalNativeGate_observe.py','FinalNativeGate_guard.py','FinalNativeGate_adapter.py','FinalNativeGate_policy.py'):
    before=blob('f56c7c533b',prefix+name);after=(D/name).read_bytes();a,b=funcs(before),funcs(after)
    identity[name]=dict(before=pin(before),after=pin(after),before_functions=a,after_functions=b,
        same_bytes_AST=sorted(k for k in b if b[k]==a.get(k)),changed=sorted(k for k in b if b[k]!=a.get(k)),
        caveat='same caller body is not unchanged whole-function semantics; runtime observation/filepin/guard helpers and catalog prerequisites changed')
    diff.extend(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='f56/'+name,tofile=name))
bundle=json.loads((D/'FinalNativeGate_reviewed.json').read_text())
for name,item in bundle.items():assert blob(item['revision'],item['path']).decode()==item['source']
# Separate setup adapter changes only fixed profile/unit/requested cap.
a=(D/'FinalNativeGate_adapter.py').read_text();b=(D/'FinalNativeGate_setup_adapter.py').read_text()
assert a.replace('high=3*c.GIB,cap=4*c.GIB','high=768*2**20,cap=c.GIB').replace("UNIT='FinalNativeGate-060'","UNIT='FinalNativeGate-pin-setup'").replace('requested=4*c.GIB if','requested=c.GIB if')==b
diff.extend(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='4G adapter',tofile='1G setup adapter'))
plan_raw=(D/'FinalNativeGate-plan.json').read_bytes();plan=json.loads(plan_raw)
seal={};exec((D/'FinalNativeGate_seal.py').read_text(),seal)
assert pin(plan_raw)['sha256']==seal['PLAN_SHA256']
for path,value in plan['files'].items():
    if path.startswith(str('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate/')):
        assert pin((D/Path(path).name).read_bytes())['sha256']==value,path
assert all(plan[k] is None for k in ('host_runtime','native_runtime_dependencies','cache_inventory','environment','inherited_limits','catalogs','setup_environment','cache_output_bounds'))
assert plan['cache_roots']==[] and plan['expected_environment_proposal']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
    node=next(n for n in ast.parse((D/name).read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
    assert len(node.body)==2 and isinstance(node.body[1],ast.Return) and node.body[1].value.value==78 and not node.args.args
changed=subprocess.check_output(['git','diff','--name-only','f56c7c533b'],cwd=ROOT,text=True).splitlines()
assert all(p.startswith((prefix,'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate/')) for p in changed)
manifest={p.name:pin(p.read_bytes()) for p in sorted(D.iterdir()) if p.is_file()}
for directory in (D,E):
    for p in directory.rglob('*'):
        if p.is_file():
            assert p.suffix not in ('.pyc','.o','.olean','.elf','.rlib','.rmeta')
            if p.suffix=='.json':assert p.stat().st_size<=5_000_000
(E/'FinalNativeGate-source-manifest-004.json').write_text(json.dumps(manifest,indent=2)+'\n')
(E/'FinalNativeGate-function-identity-004.json').write_text(json.dumps(identity,indent=2)+'\n')
(E/'FinalNativeGate-source-diff-004.txt').write_text(''.join(diff))
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(command=['python3','-B',str(D/'FinalNativeGate-repair-audit.py')],immutable_git_commands=commands,
    target='FinalNativeGate changed source and copied full-policy/1GiB integration source audit',exit=0,
    wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swaps=u.ru_nswap,
    source_revision='caa9302ede plus source-manifest-004 exact overlay',source_dependency_manifest=pin(json.dumps(manifest,sort_keys=True).encode()),
    print_axioms='N/A: Python text/AST; no Lean declaration/import invocation',
    actual_host_calls=0,actual_compiler_calls=0,actual_Kani_calls=0,security_targets_established=False,
    unresolved='owned fixed scope shutdown binding; runtime/alias/catalog/tool/cache/env/limits data and review; no activation')
(E/'FinalNativeGate-repair-audit-004.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_rss_bytes','swaps')}))
