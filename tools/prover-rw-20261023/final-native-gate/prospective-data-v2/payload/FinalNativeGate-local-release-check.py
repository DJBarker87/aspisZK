"""Local source/mock release receipt; no host, compiler or native observation."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

D=Path(__file__).resolve().parent
ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
BASE='b34142b0169312eca9f86c8fd0993715d2923b1e'
PREFIX='tools/prover-rw-20261023/final-native-gate/'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def write(name,value):
    with (E/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
def funcs(raw):return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}

def main():
    start=time.monotonic()
    manifest={str(p.relative_to(D)):pin(p.read_bytes()) for p in sorted(D.rglob('*')) if p.is_file()}
    assert all(not n.endswith(('.pyc','.elf','.olean','.o')) for n in manifest)
    assert all(v['size']<=5_000_000 for n,v in manifest.items() if n.endswith('.json'))
    write('FinalNativeGate-source-manifest-007.json',manifest)
    identity={};diff=[]
    tracked=subprocess.check_output(['git','ls-tree','--name-only',BASE,PREFIX],cwd=ROOT,text=True).splitlines()
    # Enumerate the baseline directory with Git only, not another live checkout.
    names=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,PREFIX],cwd=ROOT,text=True).splitlines()
    for path in names:
        name=Path(path).name
        if not name.endswith('.py'):continue
        before=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT);after=(D/name).read_bytes()
        a,b=funcs(before),funcs(after)
        identity[name]=dict(before=pin(before),after=pin(after),unchanged=sorted(k for k in a if a[k]==b.get(k)),changed=sorted(k for k in a if a[k]!=b.get(k)),added=sorted(set(b)-set(a)))
        if before!=after:diff.extend(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile=BASE+'/'+name,tofile='source-007/'+name))
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_scope.py','FinalNativeGate_policy.py','FinalNativeGate_adapter.py','FinalNativeGate_setup_adapter.py','FinalNativeGate_reviewed.json'):
        assert subprocess.check_output(['git','show',BASE+':'+PREFIX+name],cwd=ROOT)==(D/name).read_bytes(),name
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        main_node=next(n for n in ast.parse((D/name).read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
        assert len(main_node.body)==2 and main_node.body[-1].value.value==78
    p=json.loads((D/'FinalNativeGate-plan.json').read_bytes())
    ns={};exec((D/'FinalNativeGate_seal.py').read_bytes(),ns)
    assert pin((D/'FinalNativeGate-plan.json').read_bytes())['sha256']==ns['PLAN_SHA256']
    ns={};exec((D/'FinalNativeGate_bootstrap_seal.py').read_bytes(),ns)
    assert pin((D/'FinalNativeGate-bootstrap.json').read_bytes())['sha256']==ns['BOOTSTRAP_SHA256']
    for name,v in json.loads((D/'FinalNativeGate-bootstrap.json').read_bytes()).items():assert manifest[name]==v
    before=json.loads(subprocess.check_output(['git','show',BASE+':'+PREFIX+'FinalNativeGate-plan.json'],cwd=ROOT))
    stage='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate/'
    for key in p:
        if key not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):assert p[key]==before[key],key
    assert {k:v for k,v in p['files'].items() if not k.startswith(stage)}=={k:v for k,v in before['files'].items() if not k.startswith(stage)}
    for path,value in p['files'].items():
        if path.startswith(stage):assert manifest[Path(path).name]==dict(sha256=value,size=p['job_source_sizes'][path])
    write('FinalNativeGate-function-identity-007.json',identity)
    with (E/'FinalNativeGate-source-diff-007.txt').open('x') as f:f.write(''.join(diff))
    results=[]
    for name in ('FinalNativeGate-release-tests.py',):
        argv=[sys.executable,'-B',str(D/name)];begin=time.monotonic()
        with (E/(name+'.007.log')).open('xb') as log:
            child=subprocess.run(argv,stdout=log,stderr=subprocess.STDOUT,cwd=ROOT)
        results.append(dict(argv=argv,exit=child.returncode,wall_seconds=time.monotonic()-begin,
            log=pin((E/(name+'.007.log')).read_bytes()),source=manifest[name]))
    usage=resource.getrusage(resource.RUSAGE_SELF);children=resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt=dict(argv=[sys.executable,'-B',str(D/'FinalNativeGate-local-release-check.py')],results=results,
        exit=0 if all(x['exit']==0 for x in results) else 1,wall_seconds=time.monotonic()-start,
        self_peak_rss_bytes=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024),
        max_child_peak_rss_bytes=children.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=usage.ru_nswap+children.ru_nswap,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()+' plus exact source-manifest-007 overlay',
        source_dependency_manifest=pin(json.dumps(manifest,sort_keys=True).encode()),
        print_axioms='N/A: source text/AST/hashes and explicit Python mocks; no formal theorem/import/tool invocation',
        actual_host=0,actual_SSH=0,actual_network=0,actual_setup=0,actual_metadata=0,actual_native=0,actual_compiler=0,
        actual_Rust=0,actual_Cargo=0,actual_Kani=0,actual_Lean=0,actual_backend=0,actual_extraction=0,actual_ELF=0,
        security_targets_established=False,
        reused='Lead receipt and 37 focused tests at b34142b016 are historical evidence only; unchanged functions/policies have source identity, no new host identity gate',
        trust='existing Python/source/OS boundary; interpreter runtime bytes not newly identified; mocks establish no installed OS/native/cancellation semantics')
    write('FinalNativeGate-order-release-007.json',receipt)
    print(json.dumps(receipt,sort_keys=True))
    return receipt['exit']

if __name__=='__main__':raise SystemExit(main())
