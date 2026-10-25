"""Focused source022 closure audit and fresh reproduction; never run payload entries."""
import ast
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
E=Path(__file__).resolve().parent
ROOT=E.parents[3]
D=ROOT/'tools/prover-rw-20261023/final-native-gate'
R=D/'prospective-data-v6'
B=E/'first-v6-018e9d2aff'
STAGE='/home/dombarker/final-native-gate-v6-20261025/'
BASE='018e9d2aff669c3b1292e3ad49dfdc9a7d605620'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def dump(name,value):
    with (E/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
def module(path,name):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def definitions(raw):
    result={}
    def walk(body,prefix=''):
        for n in body:
            if isinstance(n,(ast.FunctionDef,ast.ClassDef,ast.AsyncFunctionDef)):
                key=prefix+n.name;result[key]=ast.get_source_segment(raw.decode(),n);walk(n.body,key+'.')
    walk(ast.parse(raw).body);return result

def main():
    preservation=json.loads((E/'first-v6-preservation.json').read_bytes())
    assert preservation['immutable_revision']==BASE
    for path,expected in preservation['files'].items():assert pin((B/path).read_bytes())==expected,path
    # Only new closure is inspected: git detects historical changes, no historical replay.
    tracked=subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT,text=True).splitlines()
    prefix='tools/prover-rw-20261023/final-native-gate/'
    for path in tracked:
        assert path.startswith(prefix) or path.startswith(str(E.relative_to(ROOT))+'/'),path
        assert not path.startswith(prefix+'prospective-data-v') or path.startswith(prefix+'prospective-data-v6/'),path
    maintained={p.name:p.read_bytes() for p in D.iterdir() if p.is_file()}
    changed={n for n,raw in maintained.items() if raw!=(B/n).read_bytes()}
    assert changed=={'FinalNativeGate_guard.py','FinalNativeGate-data-release-build.py','FinalNativeGate-source-refresh.py','FinalNativeGate-plan.json','FinalNativeGate-bootstrap.json','FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'},changed
    before=definitions((B/'FinalNativeGate_guard.py').read_bytes());after=definitions(maintained['FinalNativeGate_guard.py'])
    assert {n for n in before if before[n]!=after[n]}=={'Proc','Proc.cancel'}
    functions={}
    for name,keys in {'FinalNativeGate_guard.py':['Proc','Proc.cancel','Proc.operation','Proc.optional','Guard','Guard.cancel_owned','Guard.finish'],
                      'FinalNativeGate_cleanup.py':['cleanup']}.items():
        a,b=definitions((B/name).read_bytes()),definitions(maintained[name])
        functions[name]={k:dict(before=a[k],after=b[k],changed=a[k]!=b[k]) for k in keys}
    dump('complete-producer-guard-consumer-functions.json',functions)
    with (E/'source-diff.txt').open('x') as f:
        for name in sorted(changed):
            f.writelines(difflib.unified_diff((B/name).read_text().splitlines(True),maintained[name].decode().splitlines(True),fromfile='first-v6/'+name,tofile='source022/'+name))
    for location in (D,R/'payload'):
        p=json.loads((location/'FinalNativeGate-plan.json').read_bytes());old=json.loads((B/('prospective-data-v6/payload/' if location!=D else '')/'FinalNativeGate-plan.json').read_bytes())
        assert sum(v is None for v in p.values())==7
        for key in old:
            if key not in ('files','job_source_sizes','job_revision'):assert p[key]==old[key],key
        assert {k:v for k,v in p['files'].items() if not k.startswith(STAGE)}=={k:v for k,v in old['files'].items() if not k.startswith(STAGE)}
        for name in maintained:
            if name.endswith('.py') and name not in ('FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'):
                raw=(location/name).read_bytes();assert p['files'][STAGE+name]==pin(raw)['sha256'];assert p['job_source_sizes'][STAGE+name]==len(raw)
        boot=json.loads((location/'FinalNativeGate-bootstrap.json').read_bytes())
        assert boot=={n:pin((location/n).read_bytes()) for n in maintained if n not in ('FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py')}
        assert (location/'FinalNativeGate_seal.py').read_text()=='PLAN_SHA256 = '+repr(pin((location/'FinalNativeGate-plan.json').read_bytes())['sha256'])+'\n'
        assert (location/'FinalNativeGate_bootstrap_seal.py').read_text()=='BOOTSTRAP_SHA256 = '+repr(pin((location/'FinalNativeGate-bootstrap.json').read_bytes())['sha256'])+'\n'
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        main=definitions(maintained[name])['main'];tree=ast.parse(main).body[0]
        assert len(tree.body)==2 and tree.body[-1].value.value==78
    release=json.loads((R/'FinalNativeGate-release-identities.json').read_bytes())
    assert release['source_manifest']=={n:pin(raw) for n,raw in maintained.items()}
    assert set(release['changed_files'])=={'FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate-plan.json','FinalNativeGate-bootstrap.json','FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'}
    payload={p.name:pin(p.read_bytes()) for p in (R/'payload').iterdir()}
    assert payload==release['transfer_manifest']
    assert hashlib.sha256(json.dumps(payload,sort_keys=True).encode()).hexdigest()==release['transfer_manifest_root']
    for name in maintained:
        if name not in release['changed_files']:assert maintained[name]==(R/'payload'/name).read_bytes()
    for name in ('FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        a,b=definitions(maintained[name]),definitions((R/'payload'/name).read_bytes());assert {k for k in a if a[k]!=b[k]}=={'main'}
    caller=module(E/'FinalNativeGateV6-caller-template.py','source022_caller')
    assert caller.FUTURE_ALLOCATION is None;assert caller.validate_release()==release
    oldcaller=(E.with_name('FinalNativeGateV6Source-021')/'FinalNativeGateV6-caller-template.py').read_bytes()
    newcaller=(E/'FinalNativeGateV6-caller-template.py').read_bytes()
    a,b=ast.parse(oldcaller),ast.parse(newcaller)
    def without_pins(t):
        t.body=[n for n in t.body if not (isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id=='PINS' for x in n.targets))];return ast.dump(t,include_attributes=False)
    assert without_pins(a)==without_pins(b)
    pins=json.loads((E/'v6-exact-pins.json').read_bytes());assert pins['caller_template']==pin(newcaller)
    assert pins['files']==caller.PINS['files'];assert pins['transfer_manifest_root']==release['transfer_manifest_root']
    builder=module(D/'FinalNativeGate-data-release-build.py','source022_builder')
    fresh=Path(tempfile.mkdtemp(prefix='FinalNativeGateV6Source022-reproduce-'))/'prospective-data-v6';builder.prepare(fresh)
    first={str(p.relative_to(R)):pin(p.read_bytes()) for p in R.rglob('*') if p.is_file()}
    second={str(p.relative_to(fresh)):pin(p.read_bytes()) for p in fresh.rglob('*') if p.is_file()}
    assert first==second
    dump('reproduction.json',dict(byte_identical=True,files=first,path=str(fresh),host_actions=0))
    oldpins=json.loads((B/'prospective-data-v6/FinalNativeGate-release-identities.json').read_bytes())
    dependencies={str(p.relative_to(ROOT)):pin(p.read_bytes()) for p in E.with_name('FinalNativeGateV6Source-021').glob('*.py')}
    dump('reused-source-dependencies.json',dependencies)
    dump('source-manifest.json',{n:pin(raw) for n,raw in maintained.items()})
    dump('audit-result.json',dict(base=BASE,exact_claim='Mocked concrete cancellation producer/guard/consumer compatibility and prospective source022 byte closure; no actual control/native guarantee',
        old_pins={k:oldpins[k] for k in ('receiver','transport','transfer_manifest_root')},new_pins={k:release[k] for k in ('receiver','transport','transfer_manifest_root')},
        preservation_files=len(preservation['files']),payload_files=len(payload),payload_bytes=sum(v['size'] for v in payload.values()),reproduction_files=len(first),
        receiver_stage=STAGE.rstrip('/'),stage_existence='UNKNOWN; reject ANY entry',maintained_mains_disabled=4,overlay_setup_mains_only=2,final_fields_null=7,
        assumptions='Installed OS/CPython/no-untrusted-writer unchanged; no formal assumptions added or discharged',print_axioms='N/A: Python only; no Lean theorem or import',
        historical_assessment='git changed-path audit; old source021 evidence and v1-v5 unchanged; source021 source/caller tests reused only for byte/AST-identical functions',
        host_actions=0,SSH=0,Lean=0,Kani=0,native=0,keys=0,RPC=0,targets_established=False,next='STOP for lead source review; all SDK/std/runtime/extraction/sourceDrop/native/artifact/security joins OPEN; no execution allocation'))
    print(json.dumps(dict(new_pins={k:release[k] for k in ('receiver','transport','transfer_manifest_root')},payload_files=len(payload),byte_identical_reproduction=True,host_actions=0)))
if __name__=='__main__':main()
