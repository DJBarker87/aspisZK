import ast,hashlib,json,pathlib,resource,runpy,subprocess,sys,tempfile,time
start=time.monotonic();D=pathlib.Path('tools/prover-rw-20261023/final-native-gate');E=pathlib.Path(__file__).parent
base=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def old(n):return subprocess.check_output(['git','show',base+':'+str(D/n)])
def funcs(raw):return {n.name:ast.dump(n,include_attributes=False) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
ident={}
for p in D.glob('*.py'):
 before=old(p.name);after=p.read_bytes(); normalized=after.replace(b'final-native-gate-v7-20261025',b'final-native-gate-v6-20261025')
 ident[p.name]=dict(before=pin(before),after=pin(after),unchanged_functions=[k for k,v in funcs(before).items() if funcs(normalized).get(k)==v],changed_functions=[k for k,v in funcs(before).items() if funcs(normalized).get(k)!=v],added_functions=sorted(set(funcs(after))-set(funcs(before))))
 if p.name not in ('FinalNativeGate_adapter.py','FinalNativeGate_setup_adapter.py','FinalNativeGate-data-release-build.py'):
  assert funcs(before)==funcs(normalized),p.name
for n in ('FinalNativeGate_guard.py','FinalNativeGate_cleanup.py','FinalNativeGate_compact.py','FinalNativeGate_observe.py','FinalNativeGate-order-release-tests.py','FinalNativeGate-lifecycle-tests.py'):
 assert old(n)==(D/n).read_bytes(),n
release=D/'prospective-data-v7';rec=runpy.run_path(str(release/'FinalNativeGate-data-transfer.py'));rows=rec['decoded']();rec['verify'](rows)
plan=json.loads(rows['FinalNativeGate-plan.json']);assert len([k for k,v in plan.items() if v is None])==7
for n in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
 m=next(n for n in ast.parse((D/n).read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name=='main');assert any(isinstance(x,ast.Return) and isinstance(x.value,ast.Constant) and x.value.value==78 for x in ast.walk(m))
for n in ('FinalNativeGate.py','FinalNativeGate_inside.py'):assert rows[n]==(D/n).read_bytes()
caller=runpy.run_path(str(E/'FinalNativeGateV7-caller-template.py'));caller['validate_release']();assert caller['FUTURE_ALLOCATION'] is None
with tempfile.TemporaryDirectory() as t:
 dest=pathlib.Path(t)/'release';runpy.run_path(str(D/'FinalNativeGate-data-release-build.py'))['prepare'](dest)
 assert {str(p.relative_to(dest)):pin(p.read_bytes()) for p in dest.rglob('*') if p.is_file()}=={str(p.relative_to(release)):pin(p.read_bytes()) for p in release.rglob('*') if p.is_file()}
# Git diff preservation audit; only own maintained root and fresh v7 evidence/release.
changed=subprocess.check_output(['git','diff','--name-only']).decode().splitlines();assert all(p.startswith(str(D)+'/') and '/prospective-data-v' not in p for p in changed)
usage=resource.getrusage(resource.RUSAGE_SELF);assert usage.ru_maxrss<512*2**20
result=dict(argv=[sys.executable,'-B',__file__],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swap=usage.ru_nswap,source_revision=base,print_axioms='N/A source-only',identities=ident,source_pins={p.name:pin(p.read_bytes()) for p in D.iterdir() if p.is_file()},receiver_pin=pin((release/'FinalNativeGate-data-transfer.py').read_bytes()),caller_pin=pin((E/'FinalNativeGateV7-caller-template.py').read_bytes()),test_pin=pin(pathlib.Path(__file__).read_bytes()),byte_identical_reproduction=True,host_actions=0,reused_fixtures='source021/022 guard/release evidence reused only under byte/function AST identity; no old suite rerun')
(E/'closure-audit.receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('identities','source_pins')}))
