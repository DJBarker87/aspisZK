"""010 source-only focused runner; never runs remote/native/compiler commands."""
import ast, hashlib, json, os, resource, signal, subprocess, sys, time
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[2]
E=ROOT/'evidence/prover-rw-20261023/final-native-gate'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def write(path,value):
    with path.open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')
def manifest():return {p.name:pin(p.read_bytes()) for p in sorted(D.iterdir()) if p.is_file()}
def run(label,script):
    start=time.monotonic();samples=[];failure=None
    argv=[sys.executable,'-B',str(D/script)]
    with (E/(label+'.log')).open('xb') as out:
        child=subprocess.Popen(argv,stdout=out,stderr=subprocess.STDOUT,cwd=D,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),start_new_session=True)
        try:
            while True:
                raw=subprocess.check_output(['/bin/ps','-o','rss=','-p',str(os.getpid())+','+str(child.pid)],text=True)
                rss=sum(int(x)*1024 for x in raw.split());samples.append(rss)
                if rss>=512*2**20:raise RuntimeError('sampled self+child512MiB bound')
                if time.monotonic()-start>30:raise TimeoutError('30s local bound')
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:child.returncode=os.waitstatus_to_exitcode(status);break
                time.sleep(.02)
        except BaseException as exc:
            failure=repr(exc);os.killpg(child.pid,signal.SIGKILL)
            _,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
    factor=1 if sys.platform=='darwin' else 1024;own=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(target=script,argv=argv,exit=child.returncode,wall_seconds=time.monotonic()-start,
        self_peak_rss_bytes=own.ru_maxrss*factor,child_peak_rss_bytes=usage.ru_maxrss*factor,
        sampled_self_child_peak_rss_bytes=max(samples,default=0),swap=own.ru_nswap+usage.ru_nswap,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=ROOT).strip(),
        sources_and_dependencies=manifest(),interpreter=pin(Path(sys.executable).resolve().read_bytes()),
        log=pin((E/(label+'.log')).read_bytes()),control_error=failure,
        print_axioms='N/A: Python filesystem fixtures and explicit mocks; no theorem/import audit',
        SSH=0,host_actions=0,Lean=0,Kani=0,compiler=0,continuous_memory_bound=False)
    write(E/(label+'.json'),receipt)
    print(json.dumps({k:receipt[k] for k in ('target','exit','wall_seconds','self_peak_rss_bytes','child_peak_rss_bytes','sampled_self_child_peak_rss_bytes','swap','control_error')}))
    if child.returncode or failure:raise SystemExit(1)
if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit('exact local label and script required')
    run(*sys.argv[1:])
