"""One final focused source/import/preservation audit; no runtime entry execution."""
import ast
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
E=Path(__file__).resolve().parent
ROOT=E.parents[3]
D=ROOT/'tools/prover-rw-20261023/final-native-gate'
R=D/'prospective-data-v6'
B=E/'before-source020'
STAGE='/home/dombarker/final-native-gate-v6-20261025/'
OLD='/home/dombarker/final-native-gate-v5-20261025/'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def dump(name,obj):
    with (E/name).open('x') as f:json.dump(obj,f,sort_keys=True,indent=2);f.write('\n')
def definitions(raw):
    out={}
    def walk(body,prefix=''):
        for n in body:
            if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef)):
                name=prefix+n.name;out[name]=ast.get_source_segment(raw.decode(),n)
                walk(n.body,name+'.')
    walk(ast.parse(raw).body);return out

def main():
    preservation=json.loads((E/'preservation-manifest.json').read_bytes())
    for path,expected in preservation.items():assert pin((ROOT/path).read_bytes())==expected,path
    manifests={};functions={};diff=[]
    for p in sorted(D.iterdir()):
        if not p.is_file():continue
        raw=p.read_bytes();manifests[p.name]=pin(raw);before=(B/p.name).read_bytes()
        if before==raw:continue
        diff.extend(difflib.unified_diff(before.decode().splitlines(True),raw.decode().splitlines(True),fromfile='source020/'+p.name,tofile='source021/'+p.name))
        if p.suffix=='.py':
            a,b=definitions(before),definitions(raw)
            functions[p.name]={k:dict(before=a.get(k),after=b.get(k)) for k in sorted(a.keys()|b.keys()) if a.get(k)!=b.get(k)}
    allowed={'FinalNativeGate_guard.py','FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate_scope.py','FinalNativeGate-transfer-template.txt','FinalNativeGate-transport-template.txt','FinalNativeGate-data-release-build.py','FinalNativeGate-source-refresh.py','FinalNativeGate-plan.json','FinalNativeGate-bootstrap.json','FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'}
    assert {p.name for p in D.iterdir() if p.is_file() and p.read_bytes()!=(B/p.name).read_bytes()}==allowed
    for name in ('FinalNativeGate_reviewed.json','FinalNativeGate_policy.py','FinalNativeGate_adapter.py','FinalNativeGate_setup_adapter.py','FinalNativeGate_cleanup.py','FinalNativeGate_setup_observe.py','FinalNativeGate_compact.py'):
        assert (D/name).read_bytes()==(B/name).read_bytes(),name
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate_scope.py'):
        assert (D/name).read_text()==(B/name).read_text().replace(OLD.rstrip('/'),STAGE.rstrip('/')),name
    before=json.loads((B/'FinalNativeGate-plan.json').read_bytes());plan=json.loads((D/'FinalNativeGate-plan.json').read_bytes())
    assert {k:v for k,v in before['files'].items() if not k.startswith(OLD)}=={k:v for k,v in plan['files'].items() if not k.startswith(STAGE)}
    for k in before:
        if k not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):assert before[k]==plan[k],k
    assert sum(v is None for v in plan.values())==7
    assert set(plan['setup_catalog_roots'])==set(plan['native_roots'])|set(plan['files'])
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        tree=ast.parse((D/name).read_bytes());f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
        assert len(f.body)==2 and f.body[-1].value.value==78,name
    for name,expected in json.loads((D/'FinalNativeGate-bootstrap.json').read_bytes()).items():assert pin((D/name).read_bytes())==expected,name
    assert (D/'FinalNativeGate_seal.py').read_text()=='PLAN_SHA256 = '+repr(pin((D/'FinalNativeGate-plan.json').read_bytes())['sha256'])+'\n'
    assert (D/'FinalNativeGate_bootstrap_seal.py').read_text()=='BOOTSTRAP_SHA256 = '+repr(pin((D/'FinalNativeGate-bootstrap.json').read_bytes())['sha256'])+'\n'
    release=json.loads((R/'FinalNativeGate-release-identities.json').read_bytes())
    assert release['source_manifest']==manifests
    assert release['changed_files']==sorted(['FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate-plan.json','FinalNativeGate-bootstrap.json','FinalNativeGate_seal.py','FinalNativeGate_bootstrap_seal.py'])
    payload={p.name:pin(p.read_bytes()) for p in (R/'payload').iterdir()}
    assert payload==release['transfer_manifest']
    assert pin((R/'FinalNativeGate-data-transfer.py').read_bytes())==release['receiver']
    assert pin((R/'FinalNativeGate-data-transport.py').read_bytes())==release['transport']
    # Import only the disabled caller's pure helpers; validate local source pins.
    path=E/'FinalNativeGateV6-caller-template.py'
    spec=importlib.util.spec_from_file_location('final_native_v6_caller_audit',path)
    caller=importlib.util.module_from_spec(spec);spec.loader.exec_module(caller)
    assert caller.FUTURE_ALLOCATION is None
    assert caller.validate_release()==release
    tree=ast.parse(path.read_bytes())
    popens=[n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='Popen']
    assert len(popens)==1 and popens[0].args[0].elts[0].value=='/bin/ps'
    f=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
    assert len(f.body)==2 and f.body[-1].value.value==78
    pins=json.loads((E/'v6-exact-pins.json').read_bytes());assert pin(path.read_bytes())==pins['caller_template']
    assert pins['files']==caller.PINS['files'] and pins['transfer_manifest_root']==release['transfer_manifest_root']
    # Binding exact pins changes no tested helper AST except the PINS assignment.
    tested=(E/'v6-final-source-021f-source-snapshot/FinalNativeGateV6-caller-template.py').read_bytes()
    assert tested==path.read_bytes()
    dump('source-manifest.json',manifests)
    dump('source-function-before-after.json',dict(base='0f17eee7c884174bf692443cd62a313183d6f979',changes=functions,
        formal_statement_changes=None,axioms='N/A: Python source only',
        before_operational='ENOENT optional/task read handling only; ESRCH propagates even with independent absence. Original actual caller compares mutable command before poll and can lose actual exit.',
        after_operational='Only ENOENT/ESRCH plus independent matching absence may become Gone. Identity TGID/starttime envelopes, context retained; permission/unknown/live/malformed/reuse fail closed. Caller polls/reaps before liveness comparison and persists actual return code.',
        retained='Persistent guard before both admissions; original cgroup authoritative; full ResourceRssGO policy and two bounded scans; metadata512MiB/final4GiB; inside controls before acquisition. No native/refinement/security premise changed.'))
    with (E/'source-diff.txt').open('x') as f:f.write(''.join(diff))
    dump('audit-result.json',dict(exact_claim='Prospective v6 finite source, payload, seals, nonstage roots, disabled/final-null boundaries and historical preservation verified locally; not runtime/native proof',
        historical_files_verified=len(preservation),source_manifest=pin((E/'source-manifest.json').read_bytes()),
        source_seals={n:manifests[n] for n in ('FinalNativeGate-plan.json','FinalNativeGate_seal.py','FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py')},
        receiver=release['receiver'],transport=release['transport'],transfer_manifest_root=release['transfer_manifest_root'],payload_count=len(payload),payload_bytes=sum(v['size'] for v in payload.values()),
        stage=STAGE.rstrip('/'),stage_existence='UNKNOWN; reject ANY entry',mains_activated_in_overlay_only=2,maintained_mains_disabled=4,final_fields_null=7,
        host_actions=0,native_actions=0,Lean=0,Rust=0,Cargo=0,Kani=0,ELF=0,keys=0,RPC=0,axioms='N/A: no theorem/import; only Python source audit',
        targets_established=False,final_charge_authority=False,
        next='STOP for lead source/release review before ANY host action. Future allocation and actual runtime/control validation remain open.'))
    print(json.dumps(dict(historical_files_verified=len(preservation),receiver=release['receiver'],transport=release['transport'],root=release['transfer_manifest_root'],host_actions=0)))
if __name__=='__main__':main()
