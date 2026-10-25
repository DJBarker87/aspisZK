"""Bounded source-only Source029 audit. No payload imports or transport invocation."""
import ast,hashlib,json,resource,runpy,sys,tempfile,time
from pathlib import Path
D=Path('tools/prover-rw-20261023/final-native-gate').resolve()
E=Path(__file__).resolve().parent
start=time.monotonic();sys.path.insert(0,str(D))
runpy.run_path(str(D/'FinalNativeGate-source-refresh.py'))
b=runpy.run_path(str(D/'FinalNativeGate-data-release-build.py'));report=b['prepare']()
parent=Path(tempfile.mkdtemp(prefix='Source029-reproduce-',dir='/private/tmp'));r=parent/'release';b['prepare'](r)
release=D/'prospective-data-v10'
pin=lambda raw:dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
for p in release.rglob('*'):
    if p.is_file():assert p.read_bytes()==(r/p.relative_to(release)).read_bytes(),p
transport=ast.parse((release/'FinalNativeGate-data-transport.py').read_bytes())
assign={n.targets[0].id:n.value for n in transport.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name)}
canonical='/Users/dominic/ZK/.worktrees/cx-prover-rw/tools/prover-rw-20261023/final-native-gate/prospective-data-v10/FinalNativeGate-data-transfer.py'
assert ast.literal_eval(assign['RECEIVER'].args[0])==canonical
assert ast.literal_eval(assign['PIN'])==pin((release/'FinalNativeGate-data-transfer.py').read_bytes())
source=(E.parent/'FinalNativeGateV9Source-028/FinalNativeGateV9-caller-template.py').read_text()
newpins=dict(transfer_manifest_root=report['transfer_manifest_root'],files={n:pin((release/n).read_bytes()) for n in ('FinalNativeGate-data-transfer.py','FinalNativeGate-data-transport.py','FinalNativeGate-release-identities.json')})
lines=source.splitlines(True)
for i,line in enumerate(lines):
    if line.startswith('RELEASE = '):lines[i]="RELEASE = Path('tools/prover-rw-20261023/final-native-gate/prospective-data-v10')\n"
    if line.startswith('CAPTURE = '):lines[i]="CAPTURE = Path('/private/tmp/FinalNativeGateV10-future-capture-029')\n"
    if line.startswith('PINS = '):lines[i]='PINS = '+repr(newpins)+'\n'
caller=''.join(lines);(E/'FinalNativeGateV10-caller-template.py').write_text(caller)
def bodies(s):return [ast.dump(n,include_attributes=False) for n in ast.parse(s).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))]
assert bodies(source)==bodies(caller)
for base in (D,release/'payload'):
    plan=json.loads((base/'FinalNativeGate-plan.json').read_bytes());stage='/home/dombarker/final-native-gate-v10-20261025/'
    for p in base.glob('*.py'):
        if p.name in ('FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'):continue
        raw=p.read_bytes();assert plan['files'][stage+p.name]==pin(raw)['sha256'];assert plan['job_source_sizes'][stage+p.name]==len(raw)
    boot=json.loads((base/'FinalNativeGate-bootstrap.json').read_bytes())
    for name,value in boot.items():assert pin((base/name).read_bytes())==value
    for seal,target in [('FinalNativeGate_seal.py','FinalNativeGate-plan.json'),('FinalNativeGate_bootstrap_seal.py','FinalNativeGate-bootstrap.json')]:
        assert ast.literal_eval(ast.parse((base/seal).read_text()).body[0].value)==pin((base/target).read_bytes())['sha256']
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        main=next(n for n in ast.parse((base/name).read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
        if base==D or name in ('FinalNativeGate.py','FinalNativeGate_inside.py'):assert isinstance(main.body[-1],ast.Return) and main.body[-1].value.value==78
before=json.loads((E/'before/FinalNativeGate-plan.json').read_bytes());after=json.loads((D/'FinalNativeGate-plan.json').read_bytes());allowed={'files','job_source_sizes','job_revision','setup_catalog_roots'}
assert {k:v for k,v in before.items() if k not in allowed}=={k:v for k,v in after.items() if k not in allowed}
assert {k:v for k,v in before['files'].items() if not k.startswith('/home/dombarker/final-native-gate-v9-20261025/')}=={k:v for k,v in after['files'].items() if not k.startswith(stage)}
for name in ('FinalNativeGate_reviewed.json','FinalNativeGate_guard.py','FinalNativeGate_policy.py','FinalNativeGate_catalog.py','FinalNativeGate_setup_observe.py'):
    assert (D/name).read_bytes()==(E/'before'/name).read_bytes(),name
# All retained rows are replayed, including ancestors and unknowns. Neither mode reads authority from JSON.
s=(D/'FinalNativeGate_candidate.py').read_text();assert 'for path in sorted(self.rows):' in s and 'self.resolve(path)' in s
for name in ('FinalNativeGate.py','FinalNativeGate_observe.py'):
    for n in ast.walk(ast.parse((D/name).read_bytes())):
        if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='Reader':assert any(k.arg=='data_only' and isinstance(k.value,ast.Constant) and k.value.value is False for k in n.keywords)
u=resource.getrusage(resource.RUSAGE_SELF)
metrics=dict(command=['python3','-B',str(Path(__file__))],target='Source029 source refresh/build/reproduction/AST/pin audit',exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,source_revision='92a0cfa06c plus pins.json',print_axioms='N/A',private_reproduction=str(r),receiver_literal=canonical,receiver_pin=newpins['files']['FinalNativeGate-data-transfer.py'],caller_functions_unchanged=True,resource_candidate_and_contract_unchanged=True,cap_enforced=False,limit_bytes=512*2**20)
(E/'source-audit-final.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics))
