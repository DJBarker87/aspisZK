"""Finite local source/AST/Git text audit. No native or operational observation."""
import ast,difflib,hashlib,json,resource,subprocess,sys,time
from pathlib import Path
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
PREFIX='tools/prover-rw-20261023/final-native-gate/'
ENTRY='dc20aedeeeb0404719ba6e0eacc9e25a54fa58cf'
start=time.monotonic();commands=[]
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def blob(path,rev=ENTRY):
    argv=['git','show',rev+':'+path];commands.append(argv)
    return subprocess.check_output(argv,cwd=ROOT)
def funcs(raw):
    tree=ast.parse(raw);return {n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
def write(name,value):
    with (E/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
manifest={p.name:pin(p.read_bytes()) for p in sorted(D.iterdir()) if p.is_file()}
p=json.loads((D/'FinalNativeGate-plan.json').read_bytes());old=json.loads(blob(PREFIX+'FinalNativeGate-plan.json'))
ns={};exec((D/'FinalNativeGate_seal.py').read_text(),ns)
assert pin((D/'FinalNativeGate-plan.json').read_bytes())['sha256']==ns['PLAN_SHA256']
ns={};exec((D/'FinalNativeGate_bootstrap_seal.py').read_text(),ns)
assert pin((D/'FinalNativeGate-bootstrap.json').read_bytes())['sha256']==ns['BOOTSTRAP_SHA256']
bootstrap=json.loads((D/'FinalNativeGate-bootstrap.json').read_bytes())
for name,value in bootstrap.items():assert manifest[name]==value,name
assert 'FinalNativeGate-bootstrap.json' not in bootstrap and 'FinalNativeGate_bootstrap_seal.py' not in bootstrap
stage='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate/'
for path,value in p['files'].items():
    if path.startswith(stage):
        assert manifest[Path(path).name]['sha256']==value,path
        assert manifest[Path(path).name]['size']==p['job_source_sizes'][path],path
assert {k:v for k,v in p['files'].items() if not k.startswith(stage)}=={k:v for k,v in old['files'].items() if not k.startswith(stage)}
assert p['cache_roots']==[] and p['expected_environment_proposal']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
assert all(p[k] is None for k in ('host_runtime','native_runtime_dependencies','cache_inventory','environment','inherited_limits','catalogs','cache_output_bounds'))
for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
    tree=ast.parse((D/name).read_bytes());main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
    assert len(main.body)==2 and isinstance(main.body[-1],ast.Return) and main.body[-1].value.value==78
before=blob(PREFIX+'FinalNativeGate.py');after=(D/'FinalNativeGate.py').read_bytes()
a,b=funcs(before),funcs(after)
for name in ('_charge','_admit','_pins','_pins_after'):
    assert a[name]==b[name],name
for raw in (before,after):
    command=next(n for n in ast.parse(raw).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='COMMAND' for t in n.targets))
    if raw==before:old_command=ast.dump(command,include_attributes=False)
    else:assert ast.dump(command,include_attributes=False)==old_command
bundle=json.loads((D/'FinalNativeGate_reviewed.json').read_text())
for name,item in bundle.items():assert blob(item['path'],item['revision']).decode()==item['source']
identity={};diff=[]
for name in manifest:
    if name not in ('FinalNativeGate.py','FinalNativeGate_cleanup.py','FinalNativeGate_setup.py','FinalNativeGate_observe.py','FinalNativeGate_setup_observe.py','FinalNativeGate_bounded.py','FinalNativeGate_adapter.py','FinalNativeGate_setup_adapter.py'):continue
    before=blob(PREFIX+name);after=(D/name).read_bytes();a,b=funcs(before),funcs(after)
    identity[name]=dict(before=pin(before),after=pin(after),unchanged_AST=[k for k in b if a.get(k)==b[k]],changed_AST=[k for k in b if a.get(k)!=b[k]],caveat='caller AST identity alone is not transitive semantic identity; changed dependencies require focused new evidence')
    diff.extend(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile=ENTRY+'/'+name,tofile=name))
argv=['git','diff','--name-only',ENTRY];commands.append(argv)
changed=subprocess.check_output(argv,cwd=ROOT,text=True).splitlines()
assert all(x.startswith((PREFIX,'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate/')) for x in changed)
for directory in (D,E):
    for path in directory.rglob('*'):
        if path.is_file():
            assert path.suffix not in ('.pyc','.olean','.o','.elf','.rlib','.rmeta')
            if path.suffix=='.json':assert path.stat().st_size<=5_000_000
write('FinalNativeGate-source-manifest-005.json',manifest)
write('FinalNativeGate-function-identity-005.json',identity)
with (E/'FinalNativeGate-source-diff-005.txt').open('x') as f:f.write(''.join(diff))
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(command=[sys.executable,'-B',str(D/'FinalNativeGate-source-audit.py')],immutable_git_commands=commands,
             target='source-only fixed scope/bootstrap/candidate integration',exit=0,wall_seconds=time.monotonic()-start,
             peak_rss_bytes=u.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=u.ru_nswap,
             source_revision=ENTRY+' plus exact source-manifest-005 overlay',source_dependency_manifest=pin(json.dumps(manifest,sort_keys=True).encode()),
             print_axioms='N/A: Python source/AST/data; no Lean declaration or import invocation',
             actual_host=0,actual_compiler=0,actual_Kani=0,actual_Lean=0,actual_backend=0,actual_extraction=0,actual_ELF=0,
             trust='existing OS/systemd/procfs/Python/compiler/Kani/policy boundaries; no native semantics proof',
             security_targets_established=False)
write('FinalNativeGate-source-audit-005.json',receipt)
print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')}))
