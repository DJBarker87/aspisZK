"""One-use finite ancestry metadata capture; no retries or remote helpers."""
import os, sys, json, hashlib, subprocess, selectors, time, signal, resource, tempfile
from pathlib import Path
from datetime import datetime, timezone

BASE=Path(__file__).resolve().parent
PLAN=json.loads((BASE/'FinalNativeGateAncestry-plan-v2.json').read_text())
os.umask(0o077)
# macOS rejected RLIMIT_AS before any SSH attempt; retain v1 unchanged.
resource.setrlimit(resource.RLIMIT_RSS,(512*2**20,512*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,30))
signal.alarm(40)
def utc(): return datetime.now(timezone.utc).isoformat()
def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git',*args],text=True).strip()
# Refuse repeated use even after uncertain spawn/connection.
spent=BASE/'FinalNativeGateAncestry-spent.json'
fd=os.open(spent,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
capture=Path(tempfile.mkdtemp(prefix='FinalNativeGateAncestry-',dir='/private/tmp'))
start_utc=utc(); start=time.monotonic()
ledger=dict(state='SPENT before spawn; never retry',utc=start_utc,capture=str(capture),argv=PLAN['argv'],revision=git('rev-parse','HEAD'))
os.write(fd,(json.dumps(ledger,indent=2)+'\n').encode());os.fsync(fd);os.close(fd)
(capture/'spent.json').write_text(json.dumps(ledger,indent=2)+'\n')
receipt=dict(ledger,axioms='N/A (metadata only; no theorem)',script_sha256=digest(__file__),
 interpreter=str(Path(sys.executable).resolve()),interpreter_sha256=digest(Path(sys.executable).resolve()),
 ssh_sha256=digest('/usr/bin/ssh'),limits=dict(rss_bytes=512*2**20,address_space_limit="not available on this macOS invocation",cpu_seconds=30,alarm_seconds=40,ssh_wall_seconds=20,combined_output_bytes=65536),
 dependencies={str(Path(m.__file__).resolve()):digest(m.__file__) for m in (json,subprocess,selectors,resource,tempfile,hashlib,os) if getattr(m,'__file__',None) and Path(m.__file__).is_file()},
 remote_tool_hashes='unobserved; extra host commands forbidden',samples=[],spawn_attempts=1,ssh_exit=None,termination_reason=None)
pre=resource.getrusage(resource.RUSAGE_CHILDREN)
streams={'stdout':bytearray(),'stderr':bytearray()};proc=None
try:
    proc=subprocess.Popen(PLAN['argv'],stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    sel=selectors.DefaultSelector()
    for name,pipe in [('stdout',proc.stdout),('stderr',proc.stderr)]:
        os.set_blocking(pipe.fileno(),False);sel.register(pipe,selectors.EVENT_READ,name)
    deadline=time.monotonic()+20;next_sample=0
    while sel.get_map() or proc.poll() is None:
        now=time.monotonic()
        if now>=deadline and receipt['termination_reason'] is None:
            receipt['termination_reason']='local timeout20s';os.killpg(proc.pid,signal.SIGKILL)
        if now>=next_sample:
            sample=subprocess.run(['/bin/ps','-o','pid=,rss=','-p',str(os.getpid())+','+str(proc.pid)],capture_output=True,text=True,timeout=1)
            rows=[list(map(int,line.split())) for line in sample.stdout.splitlines() if line.strip()]
            receipt['samples'].append(dict(elapsed_seconds=now-start,pid_rss_kib=rows,aggregate_rss_kib=sum(r[1] for r in rows)))
            if sum(r[1] for r in rows)>=512*1024 and receipt['termination_reason'] is None:
                receipt['termination_reason']='local aggregate RSS512MiB';os.killpg(proc.pid,signal.SIGKILL)
            next_sample=now+0.1
        for key,_ in sel.select(0.05):
            data=os.read(key.fileobj.fileno(),4096)
            if not data:sel.unregister(key.fileobj);continue
            room=65536-sum(len(x) for x in streams.values())
            streams[key.data].extend(data[:room])
            if len(data)>room and receipt['termination_reason'] is None:
                receipt['termination_reason']='combined output cap exceeded; retained prefix only';os.killpg(proc.pid,signal.SIGKILL)
    receipt['ssh_exit']=proc.wait()
except BaseException as e:
    receipt['local_exception']=repr(e)
    if proc is not None and proc.poll() is None:
        os.killpg(proc.pid,signal.SIGKILL);receipt['ssh_exit']=proc.wait()
finally:
    for name,data in streams.items():
        (capture/(name+'.bin')).write_bytes(data)
        (BASE/('FinalNativeGateAncestry-'+name+'.txt')).write_bytes(data)
    post=resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt.update(end_utc=utc(),wall_seconds=time.monotonic()-start,
      output={k:dict(size=len(v),sha256=hashlib.sha256(v).hexdigest()) for k,v in streams.items()},
      sampled_peak_aggregate_rss_kib=max((s['aggregate_rss_kib'] for s in receipt['samples']),default=None),
      children_ru_maxrss_bytes_macos=post.ru_maxrss,children_ru_nswap_delta=post.ru_nswap-pre.ru_nswap,
      self_ru_maxrss_bytes_macos=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
      self_ru_nswap=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,
      measurement_limit='RSS sampled for this Python process and its SSH child only; child rusage includes local ps probes. Remote RSS/swap not observed.',
      actual_zero=['Lean','Kani','compiler','extraction','native','backend','Rust','Cargo','ELF','root','install'])
    raw=json.dumps(receipt,indent=2)+'\n'
    (capture/'receipt.json').write_text(raw)
    (BASE/'FinalNativeGateAncestry-receipt.json').write_text(raw)
    signal.alarm(0)
print(json.dumps(dict(exit=receipt['ssh_exit'],termination=receipt['termination_reason'],capture=str(capture),wall_seconds=receipt['wall_seconds'])))
