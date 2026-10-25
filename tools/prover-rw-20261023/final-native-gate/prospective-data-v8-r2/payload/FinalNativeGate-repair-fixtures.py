"""Local mock-only runner with retained status, resource and exact source pins."""
from pathlib import Path
import hashlib,json,resource,runpy,sys,time,traceback
D=Path(__file__).resolve().parent
E=D.parents[2]/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
start=time.monotonic();code=1
try:
    sys.argv=[str(D/'FinalNativeGate-repair-tests.py'),'-v']
    runpy.run_path(sys.argv[0],run_name='__main__')
except SystemExit as exc:code=exc.code or 0
except BaseException:traceback.print_exc()
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(command=['python3','-B',str(D/'FinalNativeGate-repair-fixtures.py')],
    target=[str(D/'FinalNativeGate-repair-tests.py'),'-v'],exit=code,
    wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swaps=u.ru_nswap,
    source_revision='caa9302ede plus exact source_overlay',
    source_overlay={p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in D.iterdir() if p.is_file()},
    print_axioms='N/A: Python explicit mocks and synthetic data only; no Lean declaration',
    actual_host_calls=0,actual_native_process_calls=0,actual_compiler_calls=0,actual_Kani_calls=0,
    retained_tests='28 original passes reused from f56/lead review; not rerun or promoted to current integration',
    result='local source fixtures only; both security targets NOT ESTABLISHED')
(E/'FinalNativeGate-repair-003.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ('exit','wall_seconds','peak_rss_bytes','swaps')}))
raise SystemExit(code)
