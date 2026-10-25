"""Local pure-Python fixture receipt runner. Never invokes native subprocesses."""
import contextlib
import hashlib
import json
from pathlib import Path
import resource
import runpy
import sys
import time
import traceback

D=Path(__file__).resolve().parent
E=D.parents[2]/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
run=3
while (E/f'FinalNativeGate-fixtures-{run:03}.json').exists():run+=1
prefix=f'FinalNativeGate-fixtures-{run:03}'
start=time.monotonic();code=0
sys.argv=[str(D/'FinalNativeGate-tests.py')]
with (E/(prefix+'.log')).open('x') as out,contextlib.redirect_stdout(out),contextlib.redirect_stderr(out):
    try:runpy.run_path(str(D/'FinalNativeGate-tests.py'),run_name='__main__')
    except SystemExit as exc:code=exc.code
    except BaseException:traceback.print_exc();code=1
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(command=['python3','-B',str(D/'FinalNativeGate-fixtures.py')],target=str(D/'FinalNativeGate-tests.py'),
       exit=code,wall_seconds=time.monotonic()-start,
       peak_rss_bytes=u.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=u.ru_nswap,
       source_revision='4008aeadf2 plus exact source_overlay hashes',
       source_overlay={str(p.relative_to(D.parents[2])):hashlib.sha256(p.read_bytes()).hexdigest() for p in D.iterdir() if p.is_file()},
       print_axioms='N/A: local Python synthetic fixtures; no Lean declarations',
       validation='mock integration only; no runtime/host/native semantics result',
       actual_native_body_processes=0,actual_host_queries=0)
(E/(prefix+'.json')).write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ('exit','wall_seconds','peak_rss_bytes','swap')}))
raise SystemExit(code)
