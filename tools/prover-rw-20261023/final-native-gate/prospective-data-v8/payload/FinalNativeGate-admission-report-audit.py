"""Source/import/pin review only. No operational body or remote invocation."""
import ast, difflib, hashlib, json, subprocess, sys
from pathlib import Path
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'evidence/prover-rw-20261023/final-native-gate'
BASE='ee8335334c299ef379fe23785740137d6bc4082d'
PREFIX='FinalNativeGate-admission-report'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def write(name,value):
    with (E/('admission-report-'+name)).open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')
def functions(raw):
    s=raw.decode();return {n.name:ast.get_source_segment(s,n) for n in ast.parse(s).body if isinstance(n,ast.FunctionDef)}
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def main():
    names=[PREFIX+tail for tail in ('.py','-payload.txt','-transport.py','-tests.py','-check.py','-audit.py')]
    manifest={n:pin((D/n).read_bytes()) for n in names}
    imports={}
    for n in names:
        tree=ast.parse((D/n).read_bytes());imports[n]=[]
        for node in ast.walk(tree):
            if isinstance(node,ast.Import):imports[n].extend(a.name for a in node.names)
            if isinstance(node,ast.ImportFrom):imports[n].append(node.module)
    source=(D/(PREFIX+'.py')).read_bytes();payload=(D/(PREFIX+'-payload.txt')).read_bytes()
    assert payload==source.replace(b"if __name__=='__main__':raise SystemExit(main())",b"if __name__=='__main__':raise SystemExit(diagnostic_entry())")
    tree=ast.parse((D/(PREFIX+'-transport.py')).read_bytes())
    values={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('PIN','ARGV')}
    assert values['PIN']==pin(payload)
    expected=['/usr/bin/ssh','-T','-oBatchMode=yes','-oConnectTimeout=10','-oStrictHostKeyChecking=yes','-oClearAllForwardings=yes','-oForwardAgent=no','dombarker@100.108.41.90','/usr/bin/python3 -I -B -']
    assert values['ARGV']==expected
    assert set(imports[PREFIX+'.py'])=={'hashlib','json','math','os','signal','stat'}
    changes={};diff=[]
    for old,new in (('FinalNativeGate-receipt-diagnostic.py',PREFIX+'.py'),('FinalNativeGate-receipt-transport.py',PREFIX+'-transport.py'),('FinalNativeGate-receipt-local-check.py',PREFIX+'-check.py')):
        before=(D/old).read_bytes();after=(D/new).read_bytes()
        assert before==git('show',BASE+':'+str((D/old).relative_to(ROOT)))
        a,b=functions(before),functions(after)
        changes[new]=dict(before_source=old,before_pin=pin(before),after_pin=pin(after),
                          complete_functions_before=a,complete_functions_after=b,
                          changed_functions=[k for k in sorted(set(a)|set(b)) if a.get(k)!=b.get(k)])
        diff.extend(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile=old,tofile=new))
    assert functions((D/'FinalNativeGate-receipt-transport.py').read_bytes())['_reviewed_future']==functions((D/(PREFIX+'-transport.py')).read_bytes())['_reviewed_future']
    for name in (PREFIX+'.py',PREFIX+'-transport.py','FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        body=ast.parse(functions((D/name).read_bytes())['main'])
        assert any(isinstance(n,ast.Return) and isinstance(n.value,ast.Constant) and n.value.value==78 for n in ast.walk(body))
        assert not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id in ('_reviewed_future','diagnostic_entry','_prospective','_collect','_bound_body') for n in ast.walk(body))
    capture=Path('/private/tmp/FinalNativeGate-admission-report-012-future')
    assert not capture.exists() and not capture.is_symlink()
    touched=git('diff','--name-only',BASE,'--').decode().splitlines()
    allowed=('tools/prover-rw-20261023/final-native-gate/FinalNativeGate-admission-report',
             'evidence/prover-rw-20261023/final-native-gate/admission-report-')
    assert all(n.startswith(allowed) for n in touched),touched
    # Immutable reviewed source is parsed as DATA only; no policy imports/exec.
    bundle=json.loads((D/'FinalNativeGate_reviewed.json').read_bytes())
    policy=bundle['policy']['source'];policy_functions=functions(policy.encode())
    context={n:dict(pin=pin((D/n).read_bytes()),functions=functions((D/n).read_bytes())) for n in ('FinalNativeGate_setup_observe.py','FinalNativeGate_setup_adapter.py')}
    context['embedded_policy']=dict(pin=pin(policy.encode()),evaluate=policy_functions['evaluate'],source_identity=bundle['policy']['revision'])
    write('functions-018.json',dict(base=BASE,changes=changes,context=context,premise_changes='N/A: no formal statements changed',
         original_predicate_before='regular and nlink1 and currentUID and (mode & 0o022)==0',
         original_predicate_after='regular and nlink1 and currentUID and (mode & 0o022)==0',
         claim='Bounded untrusted report diagnostic SOURCE; no source/output/security equivalence theorem'))
    with (E/'admission-report-source-diff-018.txt').open('x') as f:f.writelines(diff)
    reused={}
    for label in ('receipt-publication-011','receipt-transport-010','receipt-diagnostic-011'):
        p=E/(label+'.json');r=json.loads(p.read_bytes())
        relevant=('FinalNativeGate_setup.py','FinalNativeGate-receipt-publication-tests.py') if label.startswith('receipt-publication') else ('FinalNativeGate-receipt-transport.py','FinalNativeGate-receipt-transport-tests.py')
        reused[label]=dict(receipt=pin(p.read_bytes()),source_revision=r['source_revision'],exit=r['exit'],
            assessed_source_matches={n:r['sources_and_dependencies'].get(n)==pin((D/n).read_bytes()) for n in relevant},
            scope='Historical local fixtures only. Not rerun; no new identity or release gate.')
    old_transport=git('show','80c7917238:tools/prover-rw-20261023/final-native-gate/FinalNativeGate-receipt-transport.py')
    historical=json.loads((E/'receipt-transport-010.json').read_bytes())
    assert pin(old_transport)==historical['sources_and_dependencies']['FinalNativeGate-receipt-transport.py']
    assert functions(old_transport)['_reviewed_future']==functions((D/(PREFIX+'-transport.py')).read_bytes())['_reviewed_future']
    reused['transport_body_assessment']=dict(historical_git_revision='80c7917238',historical_pin=pin(old_transport),
        complete_reviewed_future_function_identical=True,
        literals_changed=['PAYLOAD','PIN','CAPTURE','disabled main message'],
        new_literals_validated='admission-report-tests-017: exact payload/argv/pin/disabled mains/fresh fixed capture and one durable-charge mock; no SSH')
    dependencies={}
    for name,module in sorted(sys.modules.copy().items()):
        path=getattr(module,'__file__',None)
        if path and Path(path).is_file() and (path.endswith('.py') or path.endswith('.so')):
            dependencies[name]=dict(path=path,**pin(Path(path).read_bytes()))
    future="python3 -I -B -c \"import runpy; m=runpy.run_path('"+str(D/(PREFIX+'-transport.py'))+"',run_name='reviewed_source'); raise SystemExit(m['_reviewed_future']())\""
    write('seals-018.json',dict(source_revision=git('rev-parse','HEAD').decode().strip(),base=BASE,manifest=manifest,
        imports=imports,local_audit_loaded_dependencies=dependencies,payload=pin(payload),transport=manifest[PREFIX+'-transport.py'],
        future_argv=values['ARGV'],future_local_command_NOT_EXECUTED=future,future_capture=str(capture),fixed_capture_absent=True,
        counters=dict(SSH=0,host=0,setup=0,probe=0,native=0,root=0,sudo=0,namespace=0,Lean=0,compiler=0,Kani=0,ELF=0),
        maintained_setup='UNSEALED / NO RELEASE ALLOWED',security_targets='BOTH NOT ESTABLISHED',actual_decision='UNKNOWN',
        formal_assumptions_discharged=[],new_trust_assumptions=[],retained='All existing Python/stdlib/SSH/OS, SDK/runtime/allocator/extraction/child/mark/P2Prime/native and security contract boundaries',
        axioms='N/A: no theorem, Lean, formal import audit or compiler',reused_validation=reused,
        original_raw_save='UNCHANGED ambient umask/hash-only legacy telemetry; no private-publication or actual-host-umask claim',
        budgets='Kani59/60 final reserved; privateLean240/260; extraction54/56; backend15/16; Rust2/3 actual ordinary1; ELF0/3; soundness366/368 with367/368 reserved',
        oversize_policy='No reads/parse/fetch above2MiB. Complete SHA256 unavailable for oversized report: cannot combine exact hash with hard read cap. Bounds denial with metadata, no fabricated hash.',
        next='STOP FOR LEAD REVIEW; no actual query, admission retry, scope repair, new stage or v5'))
    print(json.dumps(dict(audit='PASS',manifest=manifest,actual_SSH=0,axioms='N/A')))
if __name__=='__main__':main()
