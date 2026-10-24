#!/usr/bin/env python3
"""One local core-only Lean invocation, never a host launcher or dependency build."""
import hashlib,json,os,signal,subprocess,time
from pathlib import Path
T=Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port28rootexport-20261024'
def main():
    pre=json.loads((E/'Port28ROOTEXPORT_correction-preflight.json').read_text())
    assert pre['status'].startswith('PASS') and not pre['missing_seed_modules']
    target=T/'Port28ROOTEXPORT_Raw.lean'
    assert hashlib.sha256(target.read_bytes()).hexdigest()==pre['tool']['sha256']
    receipt=E/'Port28ROOTEXPORT_lean2.receipt.json'
    assert not receipt.exists(),'The single diagnostic slot was already charged'
    lock=Path('/tmp/aspis-local-lean.lock.d');lock.mkdir(mode=0o700)
    try:
        table=subprocess.check_output(['ps','-axo','pid=,ppid=,rss=,comm='],text=True)
        assert not any(line.split()[-1].endswith('/lean') for line in table.splitlines()),'Another local Lean is running'
        data=Path(pre['retained']);cmd=['/usr/bin/time','-l',pre['runtime'][0]['path'],'-j1','-M4400','-DElab.async=false','-R',str(T),str(target)]
        env=os.environ.copy();env['LEAN_PATH']='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean';env['PORT28_DATA']=pre['input_directory']
        r=dict(schema='Port28ROOTEXPORT-one-local-raw-diagnostic-v1',command=cmd,env={k:env[k] for k in ['LEAN_PATH','PORT28_DATA']},
            source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=False,
            tool=pre['tool'],input_manifest=pre['full_manifest'],runtime=pre['runtime'],lean_invocations_charged=1,
            print_axioms='N/A: raw-data exporter, no theorem',exit_status=None,wall_seconds=None,
            aggregate_child_hard_stop_bytes=8*1024**3,status='CHARGED before the only invocation')
        receipt.write_text(json.dumps(r,indent=2)+'\n')
        start=time.monotonic();peak=0;stop=None
        with (data/'lean2.stdout.log').open('xb') as out,(data/'lean2.stderr-time.log').open('xb') as err:
            p=subprocess.Popen(cmd,stdout=out,stderr=err,env=env,start_new_session=True,cwd=T)
            while p.poll() is None:
                table=subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True)
                rows=[tuple(map(int,l.split())) for l in table.splitlines()];ids={p.pid}
                while True:
                    nxt=ids|{pid for pid,ppid,rss in rows if ppid in ids}
                    if nxt==ids:break
                    ids=nxt
                rss=sum(rss*1024 for pid,ppid,rss in rows if pid in ids);peak=max(peak,rss)
                if rss>=8*1024**3 or time.monotonic()-start>540:
                    stop='aggregate RSS hard stop' if rss>=8*1024**3 else '540 second diagnostic bound'
                    os.killpg(p.pid,signal.SIGKILL);break
                time.sleep(.1)
            code=p.wait()
        r.update(exit_status=code,wall_seconds=time.monotonic()-start,aggregate_child_peak_rss_bytes=peak,stopped=stop,
            stdout_path=str(data/'lean2.stdout.log'),stderr_time_path=str(data/'lean2.stderr-time.log'),status='FINISHED; correction allocation exhausted; no retry authorized')
        for field,name in [('stdout','lean2.stdout.log'),('stderr_time','lean2.stderr-time.log')]:
            b=(data/name).read_bytes();r[field]=dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
        receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
    finally:lock.rmdir()
if __name__=='__main__':main()
