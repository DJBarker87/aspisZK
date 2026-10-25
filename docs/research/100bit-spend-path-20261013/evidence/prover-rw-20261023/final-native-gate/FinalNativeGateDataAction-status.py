import datetime,hashlib,json,os,resource,selectors,subprocess,time
from pathlib import Path
E=Path(__file__).resolve().parent
cfg=json.loads((E/'FinalNativeGateDataAction-status-charge.json').read_text())
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat();total=0;errors=[];peak=0
with (E/'FinalNativeGateDataAction-status.stdout').open('xb') as out,(E/'FinalNativeGateDataAction-status.stderr').open('xb') as err:
 child=subprocess.Popen(cfg['argv'],stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=dict(HOME='/Users/dominic',PATH='/usr/bin:/bin',LANG='C.UTF-8'),close_fds=True)
 try:
  with selectors.DefaultSelector() as sel:
   for stream,dest in ((child.stdout,out),(child.stderr,err)):sel.register(stream,selectors.EVENT_READ,dest)
   while sel.get_map():
    if time.monotonic()-start>20:raise TimeoutError('status20s')
    rows=subprocess.check_output(['/bin/ps','-axo','pid=,ppid=,rss='],text=True)
    procs={int(a):(int(b),int(c)*1024) for line in rows.splitlines() for a,b,c in [line.split()]}
    own={os.getpid()}
    while True:
     new={p for p,(parent,rss) in procs.items() if parent in own}-own
     if not new:break
     own|=new
    peak=max(peak,sum(procs[p][1] for p in own if p in procs))
    for key,_ in sel.select(.05):
     raw=os.read(key.fileobj.fileno(),65536)
     if not raw:sel.unregister(key.fileobj);continue
     total+=len(raw)
     if total>4194304:raise ValueError('status4MiB')
     key.data.write(raw)
  code=child.wait(timeout=max(.001,20-(time.monotonic()-start)))
 except BaseException as exc:
  errors.append(repr(exc));code=78
 finally:
  if child.poll() is None:child.kill()
  child.wait();child.stdout.close();child.stderr.close()
u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(argv=cfg['argv'],revision=revision,utc=utc,exit=code,ssh_returncode=child.returncode,wall_seconds=time.monotonic()-start,errors=errors,public_bytes=total,aggregate_peak_rss_bytes_sampled=peak,self_peak_rss_bytes=u.ru_maxrss,children_max_rss_bytes=c.ru_maxrss,swap_self=u.ru_nswap,swap_children=c.ru_nswap,print_axioms='N/A',main_ssh=1,conditional_status_ssh=1,not_GO_or_admission=True)
with (E/'FinalNativeGateDataAction-status-receipt.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True)
print(json.dumps(receipt))
