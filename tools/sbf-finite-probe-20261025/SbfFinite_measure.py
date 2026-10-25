"""One fixed local source-derivation audit receipt, no native import/execution."""
import hashlib,json,pathlib,resource,runpy,subprocess,sys,time,traceback
H=pathlib.Path(__file__).resolve().parent;O=H.parents[1]/'evidence/sbf-finite-probe-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
start=time.monotonic();exit=0;failure=None
try:runpy.run_path(str(H/'SbfFinite_audit.py'),run_name='SbfFinite_source_audit')
except BaseException:exit=1;failure=traceback.format_exc()
r=resource.getrusage(resource.RUSAGE_SELF);rss=r.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
assert rss<512*2**20
receipt=dict(command=getattr(sys,'orig_argv',sys.argv),target='SbfFinite_audit.py fixed text/AST/hash derivation',exit=exit,wall_seconds=time.monotonic()-start,peak_process_rss_bytes=rss,peak_aggregate_rss_bytes=rss,aggregate_method='single process; only Git source revision child outside measured derivation',swap=r.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),source_overlay={p.name:pin(p.read_bytes()) for p in sorted(H.iterdir()) if p.is_file()},dependencies={n:dict(path=m.__file__,**pin(pathlib.Path(m.__file__).read_bytes())) for n,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and pathlib.Path(m.__file__).is_file()},interpreter=dict(path=sys.executable,version=sys.version,**pin(pathlib.Path(sys.executable).read_bytes())),axioms='N/A; source audit only',failure=failure,actual_host_native_root_compiler_probe_install_calls=0)
idx=1
while (O/('SbfFinite-audit-attempt'+str(idx)+'.json')).exists():idx+=1
(O/('SbfFinite-audit-attempt'+str(idx)+'.json')).write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_process_rss_bytes')}));raise SystemExit(exit)
