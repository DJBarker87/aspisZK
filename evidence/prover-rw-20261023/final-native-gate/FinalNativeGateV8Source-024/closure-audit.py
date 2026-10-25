"""Source024 finite pin/identity audit only; no operational entry invocation."""
import ast,hashlib,json,pathlib,resource,runpy,subprocess,sys,tempfile,time
START=time.monotonic();BASE='c03e7860d3bc6b8e2bf1af961bffa779bfc7126a'
D=pathlib.Path('tools/prover-rw-20261023/final-native-gate');E=pathlib.Path(__file__).parent;R=D/'prospective-data-v8'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def old(p):return subprocess.check_output(['git','show',BASE+':'+str(p)])
def funcs(b):return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(b).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
def norm(b):return b.replace(b'final-native-gate-v8-20261025',b'final-native-gate-v7-20261025').replace(b'prospective-data-v8',b'prospective-data-v7')
ident={}
for p in D.glob('*.py'):
 a=old(p);b=p.read_bytes();ident[p.name]=dict(before=pin(a),after=pin(b),functions_equal=funcs(a)==funcs(norm(b)))
 if p.name!='FinalNativeGate-data-release-build.py':assert ident[p.name]['functions_equal'],p.name
for name in ('FinalNativeGate_adapter.py','FinalNativeGate_setup_adapter.py','FinalNativeGate_guard.py','FinalNativeGate_cleanup.py','FinalNativeGate_compact.py','FinalNativeGate_observe.py','FinalNativeGate-order-release-tests.py','FinalNativeGate-lifecycle-tests.py'):
 assert old(D/name)==(D/name).read_bytes(),name
before=json.loads(old(D/'FinalNativeGate_reviewed.json'));after=json.loads((D/'FinalNativeGate_reviewed.json').read_bytes())
assert {k:v for k,v in before.items() if k!='candidate'}=={k:v for k,v in after.items() if k!='candidate'}
a=ast.parse(before['candidate']['source']);b=ast.parse(after['candidate']['source'])
for tree in (a,b):tree.body=[n for n in tree.body if not isinstance(n,ast.FunctionDef) or n.name!='validate_membership']
assert ast.dump(a,include_attributes=False)==ast.dump(b,include_attributes=False)
rev='9fe9f199d1e52e3dcf4b355dff57330e5019a220';path='tools/resource-snapshot-20261025/ResourceSnapshot_candidate.py'
raw=subprocess.check_output(['git','show',rev+':'+path]);assert after['candidate']['source'].encode()==raw
node=next(n for n in ast.parse(raw).body if isinstance(n,ast.FunctionDef) and n.name=='validate_membership');function=ast.get_source_segment(raw.decode(),node)
fnsha=hashlib.sha256((function+'\n').encode()).hexdigest();assert fnsha=='a3cc528a389d9baa320854fe299af2714b13cc207301b4ee0126106de9a0a8f8',fnsha
caller=E/'FinalNativeGateV8-caller-template.py';previous=E.parent/'FinalNativeGateV7Source-023/FinalNativeGateV7-caller-template.py'
assert funcs(previous.read_bytes())==funcs(caller.read_bytes())
c=runpy.run_path(str(caller));report=c['validate_release']();assert c['FUTURE_ALLOCATION'] is None
assert str(c['CAPTURE'])=='/private/tmp/FinalNativeGateV8-future-capture-024'
assert len(report['transfer_manifest'])==68
receiver=runpy.run_path(str(R/'FinalNativeGate-data-transfer.py'));rows=receiver['decoded']();receiver['verify'](rows)
plan=json.loads(rows['FinalNativeGate-plan.json']);assert sum(v is None for v in plan.values())==7
for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
 main=next(n for n in ast.parse((D/name).read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name=='main');assert any(isinstance(n,ast.Return) and isinstance(n.value,ast.Constant) and n.value.value==78 for n in ast.walk(main))
for name in ('FinalNativeGate.py','FinalNativeGate_inside.py'):assert rows[name]==(D/name).read_bytes()
assert set(report['changed_files'])=={'FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate-plan.json','FinalNativeGate_seal.py','FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py'}
oldplan=json.loads(old(D/'FinalNativeGate-plan.json'))
for k,v in oldplan.items():
 if k not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):assert plan[k]==v,k
external=lambda p:{k:v for k,v in p['files'].items() if '/final-native-gate-v' not in k}
assert external(oldplan)==external(plan)
with tempfile.TemporaryDirectory() as t:
 dest=pathlib.Path(t)/'release';runpy.run_path(str(D/'FinalNativeGate-data-release-build.py'))['prepare'](dest)
 assert {str(p.relative_to(dest)):pin(p.read_bytes()) for p in dest.rglob('*') if p.is_file()}=={str(p.relative_to(R)):pin(p.read_bytes()) for p in R.rglob('*') if p.is_file()}
# Preserve ten original join method ASTs; superseded count rejection is not reused.
oldjoins=E.parent/'FinalNativeGateV7Source-023/resource-joins.py'
a=next(n for n in ast.parse(oldjoins.read_bytes()).body if isinstance(n,ast.ClassDef) and n.name=='Joins');b=next(n for n in ast.parse((E/'resource-joins.py').read_bytes()).body if isinstance(n,ast.ClassDef) and n.name=='Joins')
unchanged=[x.name for x in a.body if isinstance(x,ast.FunctionDef) and any(isinstance(y,ast.FunctionDef) and y.name==x.name and ast.dump(x,include_attributes=False)==ast.dump(y,include_attributes=False) for y in b.body)]
assert len([n for n in unchanged if n.startswith('test_')])==9
changed=subprocess.check_output(['git','diff','--name-only']).decode().splitlines();assert all(p.startswith(str(D)+'/') and '/prospective-data-v' not in p for p in changed)
r=resource.getrusage(resource.RUSAGE_SELF);assert r.ru_maxrss<512*2**20
out=dict(argv=[sys.executable,'-B',__file__],exit=0,wall_seconds=time.monotonic()-START,peak_rss_bytes=r.ru_maxrss,swap=r.ru_nswap,source_revision=BASE,print_axioms='N/A',host_actions=0,candidate=dict(revision=rev,path=path,**pin(raw),validate_membership_sha256=fnsha),identities=ident,unchanged_join_methods=unchanged,reused_evidence='021/022/023 guard/release and unaffected joins under byte/function AST identity; obsolete count rejection superseded, not reused',byte_identical_reproduction=True,source_pins={p.name:pin(p.read_bytes()) for p in D.iterdir() if p.is_file()},release_pins={str(p.relative_to(R)):pin(p.read_bytes()) for p in R.rglob('*') if p.is_file()},caller_pin=pin(caller.read_bytes()),test_pins={p.name:pin(p.read_bytes()) for p in E.glob('*.py')})
(E/'closure-audit.receipt.json').write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(json.dumps({k:out[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap','byte_identical_reproduction')}))
