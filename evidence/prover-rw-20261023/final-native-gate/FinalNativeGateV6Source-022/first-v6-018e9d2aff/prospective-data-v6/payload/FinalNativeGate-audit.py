"""Local Python/text audit; subprocess use is ONLY immutable Git blob reads.
No host metadata, native compiler/parser, solver or workload invocation.
"""
from pathlib import Path
import ast
import difflib
import hashlib
import json
import resource
import subprocess
import time

D=Path(__file__).resolve().parent
ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
start=time.monotonic()
commands=[]
def blob(rev,path):
    argv=['git','show',rev+':'+path];commands.append(argv)
    return subprocess.check_output(argv,cwd=ROOT).decode()
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
def funcs(s):
    result={}
    def walk(nodes,prefix=''):
        for n in nodes:
            if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)):
                result[prefix+n.name]=n
            elif isinstance(n,ast.ClassDef):walk(n.body,prefix+n.name+'.')
    walk(ast.parse(s).body)
    return {k:dict(bytes_sha256=sha(ast.get_source_segment(s,n)),ast_sha256=sha(ast.dump(n,include_attributes=False))) for k,n in result.items()}

pairs={
 'FinalNativeGate_policy.py':'ResourceRssGOv3_sources.py',
 'FinalNativeGate_adapter.py':'ResourceRssGOv3_adapter.py',
 'FinalNativeGate_guard.py':'ResourceRssGOv3_guard.py',
 'FinalNativeGate_observe.py':'ResourceRssGOv3_host.py'}
assessment={};diff=[]
for new,old in pairs.items():
    path='tools/resource-rss-go-v3-20261025/'+old
    a=blob('45d137dd34',path);b=(D/new).read_text();fa,fb=funcs(a),funcs(b)
    same={k:v for k,v in fb.items() if fa.get(k)==v}
    changed={k:dict(before=fa.get(k),after=v) for k,v in fb.items() if fa.get(k)!=v}
    assessment[new]=dict(original_revision='45d137dd34',original_path=path,
                        original_sha256=sha(a),current_sha256=sha(b),
                        unchanged_function_bytes_and_AST=same,changed_or_new_functions=changed,
                        omitted_original_functions=sorted(set(fa)-set(fb)))
    diff.extend(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile=path,tofile=new))
# Every complete policy/dependency byte string must match immutable reviewed Git.
bundle=json.loads((D/'FinalNativeGate_reviewed.json').read_text())
for k,entry in bundle.items():
    expected=blob(entry['revision'],entry['path'])
    assert expected==entry['source'] and sha(expected)==entry['sha256']
    assert len(expected.encode())==entry['size']
    assessment['policy_bundle:'+k]=dict(byte_identity=True,AST_identity=True,
                                        source_revision=entry['revision'],path=entry['path'],sha256=sha(expected),
                                        function_hashes=funcs(expected))
# Only introduced paths changed since manager's exact parked entry.
argv=['git','diff','--name-only','dcc848acfc'];commands.append(argv)
changed=subprocess.check_output(argv,cwd=ROOT,text=True).splitlines()
allowed=('tools/prover-rw-20261023/final-native-gate/','docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate/')
assert all(p.startswith(allowed) for p in changed),changed
# Exact body/module hashes in sealed local plan (bootstrap is independently pinned).
plan=json.loads((D/'FinalNativeGate-plan.json').read_text())
ns={};exec((D/'FinalNativeGate_seal.py').read_text(),ns)
assert hashlib.sha256((D/'FinalNativeGate-plan.json').read_bytes()).hexdigest()==ns['PLAN_SHA256']
for name in pairs.keys() | {'FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_reviewed.json'}:
    host='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate/'+name
    assert plan['files'][host]==hashlib.sha256((D/name).read_bytes()).hexdigest(),name
assert all(plan[k] is None for k in ('host_runtime','native_runtime_dependencies','cache_inventory','environment','inherited_limits'))
# Public entry remains an unconditional literal78, independent of globals/flags.
for name in ('FinalNativeGate.py','FinalNativeGate_inside.py'):
    main=next(n for n in ast.parse((D/name).read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
    assert len(main.body)==2 and isinstance(main.body[0],ast.Expr)
    assert isinstance(main.body[1],ast.Return) and isinstance(main.body[1].value,ast.Constant) and main.body[1].value.value==78
    assert not main.args.args
for path in [*D.rglob('*'),*E.rglob('*')]:
    if path.is_file():
        assert path.suffix not in ('.pyc','.o','.olean','.elf','.rlib','.rmeta'),path
        if path.suffix=='.json':assert path.stat().st_size<=5_000_000,path
(E/'FinalNativeGate-source-diff-002.txt').write_text(''.join(diff))
(E/'FinalNativeGate-function-identity-002.json').write_text(json.dumps(assessment,indent=2)+'\n')
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(command=['python3','-B',str(D/'FinalNativeGate-audit.py')],
             immutable_git_commands=commands,target='local Python source/policy identity and path/disabled-entry audit',
             exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,
             source_revision='4008aeadf2 plus exact source_overlay hashes',
             source_overlay={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.iterdir() if p.is_file()},
             print_axioms='N/A: no Lean theorem or import; Python text/AST only',
             result='SOURCE AUDIT ONLY; live admission/native semantics/security targets NOT established',
             actual_host_queries=0,actual_native_body_processes=0)
(E/'FinalNativeGate-audit-receipt-002.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')}))
