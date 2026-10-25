"""Python-only focused test receipt. Never host/native/compiler operations."""
import hashlib,json,os,resource,subprocess,sys,time
from pathlib import Path
D=Path(__file__).resolve().parent
E=D.parents[2]/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/final-native-gate'
number=sys.argv[1]
if not number.isdecimal():raise ValueError('attempt number')
argv=[sys.executable,'-B',str(D/'FinalNativeGate-lifecycle-tests.py')]
manifest={p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in sorted(D.iterdir()) if p.is_file()}
start=time.monotonic()
with (E/('FinalNativeGate-lifecycle-'+number+'.log')).open('xb') as out:
    p=subprocess.Popen(argv,stdout=out,stderr=subprocess.STDOUT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
    _,status,u=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
peak=u.ru_maxrss*(1 if sys.platform=='darwin' else 1024)
receipt=dict(command=argv,exit=p.returncode,wall_seconds=time.monotonic()-start,peak_rss_bytes=peak,swaps=u.ru_nswap,
             source_revision='af823de916 plus exact embedded source/dependency overlay',source_dependencies=manifest,
             print_axioms='N/A: Python mocks/synthetic data; no theorem or import audit',
             actual_host=0,actual_compiler=0,actual_Kani=0,actual_Lean=0,actual_extraction=0,actual_backend=0,actual_ELF=0,
             local_test_below512MiB=peak<512*2**20)
with (E/('FinalNativeGate-lifecycle-'+number+'.json')).open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
print(json.dumps({k:receipt[k] for k in ('exit','wall_seconds','peak_rss_bytes','swaps')}))
print((E/('FinalNativeGate-lifecycle-'+number+'.log')).read_text())
raise SystemExit(p.returncode)
