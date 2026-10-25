"""Finite local source preparation/explicit mocks; sampled owned-child RSS control.
No rlimit setters, host actions, native backends or compiler invocation.
Each child has a 30s wall deadline and sampled 512MiB RSS ceiling; not a
continuous allocation limit or a native cancellation theorem.
"""
import ast
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time

D=Path(__file__).resolve().parent
ROOT=D.parents[2]
E=ROOT/'evidence/prover-rw-20261023/final-native-gate'
BASE='c67d0a3d5a0b4d53ec9a7431e8ba70c8a31c93e2'
PREFIX='tools/prover-rw-20261023/final-native-gate/'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def source_manifest():return {p.name:pin(p.read_bytes()) for p in sorted(D.iterdir()) if p.is_file()}
def write(name,value):
    with (E/name).open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')
def functions(raw):
    return {n.name:ast.get_source_segment(raw.decode(),n) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}

def main():
    E.mkdir(parents=True,exist_ok=True)
    packet=Path(tempfile.mkdtemp(prefix='FinalNativeGate-v4-source-',dir='/private/tmp'))
    results=[]
    revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=ROOT).strip()
    def run(name,argv):
        start=time.monotonic();samples=[];failure=None
        with (E/(name+'.log')).open('xb') as log:
            child=subprocess.Popen(argv,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,
                env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),start_new_session=True)
            try:
                while True:
                    # Only the two known owned test processes; no machine-wide
                    # process/cache inventory. Test children never spawn native jobs.
                    raw=subprocess.check_output(['/bin/ps','-o','rss=','-p',str(os.getpid())+','+str(child.pid)],text=True)
                    rss=sum(int(x)*1024 for x in raw.split());samples.append(rss)
                    if rss>512*2**20:raise RuntimeError('sampled local self+child512MiB ceiling')
                    if time.monotonic()-start>30:raise TimeoutError('local child30s deadline')
                    pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                    if pid:
                        child.returncode=os.waitstatus_to_exitcode(status);break
                    time.sleep(.02)
            except BaseException as exc:
                failure=repr(exc);os.killpg(child.pid,signal.SIGKILL)
                _,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
        self_usage=resource.getrusage(resource.RUSAGE_SELF)
        factor=1 if sys.platform=='darwin' else 1024
        result=dict(target=name,argv=argv,exit=child.returncode,wall_seconds=time.monotonic()-start,
            self_peak_rss_bytes=self_usage.ru_maxrss*factor,child_peak_rss_bytes=usage.ru_maxrss*factor,
            sampled_self_child_peak_rss_bytes=max(samples,default=0),samples=len(samples),
            swap=self_usage.ru_nswap+usage.ru_nswap,control_error=failure,
            source_revision=revision,source_dependencies=source_manifest(),
            interpreter=pin(Path(sys.executable).resolve().read_bytes()),log=pin((E/(name+'.log')).read_bytes()),
            print_axioms='N/A: source preparation / explicit mocks; no formal import or theorem')
        write(name+'.json',result);results.append(result)
        print(json.dumps({k:result[k] for k in ('target','exit','wall_seconds','child_peak_rss_bytes','sampled_self_child_peak_rss_bytes','control_error')}),flush=True)
        if failure or child.returncode:raise RuntimeError('retained failed target '+name)
    run('v4-refresh-009',[sys.executable,'-B',str(D/'FinalNativeGate-source-refresh.py')])
    run('v4-build-009',[sys.executable,'-B',str(D/'FinalNativeGate-data-release-build.py')])
    for name in ('FinalNativeGate-v4-tests.py','FinalNativeGate-order-release-tests.py'):
        run(name+'.009',[sys.executable,'-B',str(D/name)])
    # Independent fresh output: rerun the finite deterministic builder into a
    # private fresh destination, never overwrite/adopt a release directory.
    code="import runpy; m=runpy.run_path("+repr(str(D/'FinalNativeGate-data-release-build.py'))+",run_name='source_review'); m['prepare']("+repr(str(packet/'reproduction'))+")"
    run('v4-reproduction-009',[sys.executable,'-B','-c',code])
    release=D/'prospective-data-v4';fresh=packet/'reproduction'
    left={str(p.relative_to(release)):pin(p.read_bytes()) for p in sorted(release.rglob('*')) if p.is_file()}
    right={str(p.relative_to(fresh)):pin(p.read_bytes()) for p in sorted(fresh.rglob('*')) if p.is_file()}
    assert left==right,'fresh v4 reproduction differs'
    write('FinalNativeGate-v4-reproduction-009.json',dict(files=left,byte_identical=True,retained_fresh_location=str(fresh)))
    manifest=source_manifest();write('FinalNativeGate-source-manifest-009.json',manifest)
    changes={}
    # Exact changed top-level source only; no full historical inventory replay.
    for name in manifest:
        proc=subprocess.run(['git','show',BASE+':'+PREFIX+name],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if proc.returncode:continue
        before=proc.stdout;after=(D/name).read_bytes()
        if before==after:continue
        row=dict(before_pin=pin(before),after_pin=pin(after))
        if name.endswith('.py'):
            a,b=functions(before),functions(after)
            row['complete_changed_functions']={k:dict(before=a.get(k),after=b.get(k)) for k in sorted(set(a)|set(b)) if a.get(k)!=b.get(k)}
        changes[name]=row
    write('FinalNativeGate-source-functions-009.json',dict(base=BASE,changes=changes,
        caveat='Complete changed function/class statements; module-level constants and all text deltas are in source-diff-009.txt. No historical-v3 identity assertion.'))
    diff=subprocess.check_output(['git','diff',BASE,'--',PREFIX],cwd=ROOT)
    with (E/'FinalNativeGate-source-diff-009.txt').open('xb') as f:f.write(diff)
    write('FinalNativeGate-v4-summary-009.json',dict(source_revision=revision,source_manifest=manifest,release=left,
        results=[dict(target=r['target'],exit=r['exit'],wall_seconds=r['wall_seconds']) for r in results],
        print_axioms='N/A',source_only=True,host_actions=0,SSH=0,setup=0,compiler=0,Kani=0,Lean=0,
        target_established=False,continuous_memory_bound=False,
        runtime_boundary='Python/stdlib and OS trusted operationally; interpreter file pinned, no whole-runtime semantics claim',
        historical_reuse='c67d0a3d5a source and v3 retained; lead ancestry/actual-action and pre-SSH limit failures are prior observations only, no new host identity gate'))
    return 0

if __name__=='__main__':raise SystemExit(main())
