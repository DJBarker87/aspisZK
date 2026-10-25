"""Local bounded fixture/source runner. No host/native/compiler/permission setters.
Sampled self+owned-child RSS ceiling512MiB, deadline30s; no allocation theorem.
"""
import hashlib,json,os,resource,signal,subprocess,sys,tempfile,time
import ast,base64,contextlib,copy,difflib,fcntl,importlib.util,selectors,stat,sysconfig,unittest,unittest.mock,zoneinfo
from pathlib import Path
D=Path(__file__).resolve().parent
ROOT=D.parents[2]
E=ROOT/'evidence/prover-rw-20261023/final-native-gate'
BASE='e8ffe0b688735e46e397c7aa0c0b2e8aa3c68b7e'
PREFIX='tools/prover-rw-20261023/final-native-gate/'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def manifest():return {p.name:pin(p.read_bytes()) for p in sorted(D.iterdir()) if p.is_file()}
def write(name,value):
    with (E/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')

def run(name,argv):
    start=time.monotonic();samples=[];error=None
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    sources=manifest()
    with (E/(name+'.log')).open('xb') as log:
        child=subprocess.Popen(argv,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,
            env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),start_new_session=True)
        try:
            while True:
                rss=sum(int(x)*1024 for x in subprocess.check_output(['/bin/ps','-o','rss=','-p',str(os.getpid())+','+str(child.pid)],text=True).split());samples.append(rss)
                if rss>512*2**20:raise RuntimeError('sampled512MiB ceiling')
                if time.monotonic()-start>30:raise TimeoutError('30s fixture deadline')
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:child.returncode=os.waitstatus_to_exitcode(status);break
                time.sleep(.02)
        except BaseException as exc:
            error=repr(exc);os.killpg(child.pid,signal.SIGKILL)
            _,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
    own=resource.getrusage(resource.RUSAGE_SELF);factor=1 if sys.platform=='darwin' else 1024
    receipt=dict(target=name,argv=argv,exit=child.returncode,wall_seconds=time.monotonic()-start,
        peak_rss_bytes=usage.ru_maxrss*factor,self_peak_rss_bytes=own.ru_maxrss*factor,
        sampled_self_child_peak_rss_bytes=max(samples,default=0),swap=usage.ru_nswap+own.ru_nswap,
        source_revision=revision,source_dependency_hashes=sources,interpreter=pin(Path(sys.executable).resolve().read_bytes()),
        runtime=dict(version=sys.version,platform=sys.platform,modules={
            name:dict(path=str(Path(m.__file__).resolve()),**pin(Path(m.__file__).resolve().read_bytes()))
            for name,m in sorted(sys.modules.items()) if getattr(m,'__file__',None) and
            Path(m.__file__).is_file() and str(Path(m.__file__).resolve()).startswith(sysconfig.get_path('stdlib')+'/')}),control_error=error,log=pin((E/(name+'.log')).read_bytes()),
        print_axioms='N/A: Python source fixtures; no Lean theorem/import',host_actions=0)
    write(name+'.json',receipt)
    print(json.dumps({k:receipt[k] for k in ('target','exit','wall_seconds','peak_rss_bytes','swap','control_error')}))
    if error or child.returncode:raise SystemExit(1)


def main():
    # Unique explicit attempt names; failures and old reports are never replaced.
    name=sys.argv[1];argv=sys.argv[2:]
    if not name.startswith('v5-') or '/' in name:raise ValueError('v5 evidence basename')
    run(name,argv)

if __name__=='__main__':main()
