"""Fixed local source/mock-only repair validation; no install/native/host action."""
import hashlib,json,pathlib,resource,subprocess,sys,time,traceback
START=time.monotonic();H=pathlib.Path(__file__).resolve().parent;O=H.parents[1]/'evidence/sbf-finite-probe-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def overlay():return {p.name:pin(p.read_bytes()) for p in H.iterdir() if p.is_file()}
revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
steps=[];failure=None;exit=0
outputs=['SbfFinite-installation.json','SbfFinite-statements-and-identities.json','SbfFinite-delta.patch.txt','SbfFinite-entry-repair-statements.json']
def call(script,*args):
 command=[sys.executable,'-B',str(H/script),*args];start=time.monotonic()
 p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 steps.append(dict(command=command,exit=p.returncode,wall_seconds=time.monotonic()-start,output=p.stdout.decode()))
 if p.returncode:raise RuntimeError(script+' failed; retained receipt/log')
 return p
try:
 before=overlay()
 call('SbfFinite_audit.py')
 generated={n:pin((O/n).read_bytes()) for n in outputs}
 call('SbfFinite_audit.py')
 assert generated=={n:pin((O/n).read_bytes()) for n in outputs},'report regeneration not byte-consistent'
 assert before==overlay(),'committed source regeneration not byte-consistent'
 previous={p.name for p in O.glob('SbfFinite-tests-attempt*.json')}
 call('SbfFinite_run_tests.py')
 new={p.name for p in O.glob('SbfFinite-tests-attempt*.json')}-previous
 assert len(new)==1;test_receipt=new.pop()
 call('SbfFinite_check.py',test_receipt)
except BaseException:
 exit=1;failure=traceback.format_exc()
r=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN);factor=1 if sys.platform=='darwin' else 1024
if (r.ru_maxrss+c.ru_maxrss)*factor>=512*2**20:exit=1;failure=str(failure)+' resource peak-sum exceeds512MiB'
report=dict(schema='SbfFinite-installer-entry-repair-validation-v1',command=getattr(sys,'orig_argv',sys.argv),source_revision=revision,exit=exit,failure=failure,steps=steps,
 wall_seconds=time.monotonic()-START,peak_process_rss_bytes=r.ru_maxrss*factor,child_peak_rss_bytes=c.ru_maxrss*factor,peak_aggregate_rss_bytes=None,
 aggregate_peak_upper_bound_bytes=(r.ru_maxrss+c.ru_maxrss)*factor,aggregate_method='concurrent aggregate UNOBSERVED; conservative parent plus serial child peak sum; nested Git peaks reported separately in child receipts',swap=r.ru_nswap,child_swaps=c.ru_nswap,
 source_overlay=overlay(),regenerated_reports=locals().get('generated'),tests=locals().get('test_receipt'),
 dependencies={n:dict(path=m.__file__,**pin(pathlib.Path(m.__file__).read_bytes())) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and pathlib.Path(m.__file__).is_file()},
 interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable).read_bytes())),axioms='N/A; Python source/AST/hash and explicit OS/import mocks only',
 actual_budgets=dict(host=0,SSH=0,network=0,root=0,sudo=0,namespace=0,native=0,probe=0,install=0,compiler=0,Lean=0,Rust=0,Cargo=0,Kani=0,extraction=0,backend=0,ELF=0),
 both_security_targets='NOT ESTABLISHED',status='STOP_FOR_LEAD_REVIEW',derived_JSON_over5MB=[])
i=1
while (O/('SbfFinite-entry-repair-validation'+str(i)+'.json')).exists():i+=1
raw=(json.dumps(report,indent=2,sort_keys=True)+'\n').encode();assert len(raw)<5_000_000
(O/('SbfFinite-entry-repair-validation'+str(i)+'.json')).write_bytes(raw)
print(json.dumps(dict(exit=exit,failure=failure,steps=len(steps),wall_seconds=report['wall_seconds'],self_rss=report['peak_process_rss_bytes'],serial_child_peak=report['child_peak_rss_bytes'])));raise SystemExit(exit)
