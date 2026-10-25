"""Local explicit source/synthetic suite receipt; no child/native/kernel probe."""
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
import traceback
import unittest
H=Path(__file__).resolve().parent;O=H.parents[1]/'evidence/sbf-finite-probe-20261025'
START=time.monotonic()
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
# Choose monotonically new retained receipt name; no historical failure rewritten.
idx=1
while (O/('SbfFinite-tests-attempt'+str(idx)+'.json')).exists():idx+=1
stream=io.StringIO();passed=False;exception=None
try:
 spec=importlib.util.spec_from_file_location('SbfFinite_tests',H/'SbfFinite_tests.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 with contextlib.redirect_stdout(stream),contextlib.redirect_stderr(stream):
  result=unittest.TextTestRunner(stream=stream,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromName(sys.argv[1],m) if len(sys.argv)>1 else unittest.defaultTestLoader.loadTestsFromModule(m))
 passed=result.wasSuccessful();count=result.testsRun
except BaseException:
 exception=traceback.format_exc();stream.write(exception);count=0
raw=stream.getvalue().encode();(O/('SbfFinite-tests-attempt'+str(idx)+'.log')).write_bytes(raw)
revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip()
children=resource.getrusage(resource.RUSAGE_CHILDREN)
child_rss=children.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
usage=resource.getrusage(resource.RUSAGE_SELF);rss=usage.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
if rss+child_rss>=512*2**20:
 passed=False;exception='synthetic source validation limit exceeded (self+child peak sum)' 
deps={}
for n,m in sorted(sys.modules.items()):
 p=getattr(m,'__file__',None)
 if p:
  p=Path(p)
  if p.is_file():deps[n]=dict(path=str(p),**pin(p.read_bytes()))
receipt=dict(command=getattr(sys,'orig_argv',sys.argv),exit=0 if passed else 1,wall_seconds=time.monotonic()-START,
 peak_process_rss_bytes=rss,peak_aggregate_rss_bytes=None,aggregate_peak_upper_bound_bytes=rss+child_rss,child_peak_rss_bytes=child_rss,child_swaps=children.ru_nswap,aggregate_method='Concurrent peak UNOBSERVED; conservative self plus serial Git child peaks; tests use no children or real threads',
 swap=usage.ru_nswap,source_revision=revision,
 source_overlay={p.name:pin(p.read_bytes()) for p in sorted(H.iterdir()) if p.is_file()},dependencies=deps,
 interpreter=dict(path=sys.executable,version=sys.version,**pin(Path(sys.executable).read_bytes())),
 axioms='N/A; Python source and explicit mocks, no theorem/compiler/native gate',tests=count,exception=exception,log=pin(raw),
 actual_budgets=dict(host=0,SSH=0,network=0,root=0,native=0,compiler=0,Lean=0,Rust=0,Cargo=0,Kani=0,extraction=0,backend=0,ELF=0,probe=0,install=0),
 reused='immutable source policy functions executed only on new synthetic raw inputs; historical actual acquisition/lead review reused, no identity gate rerun')
(O/('SbfFinite-tests-attempt'+str(idx)+'.json')).write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(raw.decode());print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_process_rss_bytes','tests')}));raise SystemExit(receipt['exit'])
