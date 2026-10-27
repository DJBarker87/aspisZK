"""Reproduce evidence-only v2.1 copies from unchanged preregistered tools."""
from pathlib import Path
root=Path(__file__).resolve().parents[4]
out=Path(__file__).resolve().parent
w=(root/'tools/pv-dudect/window_worker.py').read_text()
w=w.replace('import pathlib,subprocess,os,json,time,sys,signal', 'import pathlib,subprocess,os,json,time,sys,signal,threading,ctypes,struct,select\nfrom thermal_monitor import snapshot, excluded')
a=w.index(" for p in pathlib.Path('/sys/class/thermal')")
b=w.index('\n # Reject other finite-memory',a)
w=w[:a]+" thermal=snapshot()\n assert thermal['package_c']<=95, 'package exceeds 95 C: '+str(thermal['package_c'])\n"+w[b:]
w=w.replace("return {'epoch':time.time(),", "return {'thermal':thermal,'epoch':time.time(),")
w=w.replace("child=None;t=time.monotonic();reason=None",'''# Observe file boundaries without changing the pinned executable or its intervals.
lib=ctypes.CDLL(None, use_errno=True)
fd=lib.inotify_init1(os.O_NONBLOCK|os.O_CLOEXEC)
assert fd>=0
assert lib.inotify_add_watch(fd, os.fsencode(O), 0x100|0x8)>=0
boundary_stop=threading.Event(); boundary_errors=[]
def boundaries():
 try:
  with (O/'experiment-boundaries.jsonl').open('x') as log:
   while not boundary_stop.is_set() or select.select([fd],[],[],0)[0]:
    if not select.select([fd],[],[],0.05)[0]: continue
    data=os.read(fd,65536); off=0
    while off<len(data):
     wd,mask,cookie,n=struct.unpack_from('iIII',data,off); off+=16
     name=data[off:off+n].split(b'\\0',1)[0].decode(); off+=n
     if mask & 0x4000: raise RuntimeError('inotify overflow')
     if not name.endswith('.csv'): continue
     row=dict(family=name[:-4], boundary='start-before-warmup' if mask & 0x100 else 'end-after-flush', **snapshot())
     log.write(json.dumps(row)+'\\n'); log.flush()
 except BaseException as e: boundary_errors.append(str(e))
boundary_thread=threading.Thread(target=boundaries)
child=None;t=time.monotonic();reason=None''')
w=w.replace("guard();subprocess.run", "guard();rec['excluded_thermal_zones']=excluded();subprocess.run")
w=w.replace("  child=subprocess.Popen", "  boundary_thread.start()\n  child=subprocess.Popen")
w=w.replace("mon.write(json.dumps(guard())+'\\n');mon.flush();time.sleep(1)", "assert not boundary_errors, str(boundary_errors)\n   mon.write(json.dumps(guard())+'\\n');mon.flush();time.sleep(1)")
w=w.replace("finally:\n rec.update", "finally:\n boundary_stop.set()\n if boundary_thread.ident is not None:boundary_thread.join(timeout=3)\n os.close(fd)\n if boundary_errors:reason='boundary sensor error: '+str(boundary_errors)\n rec.update")
(out/'window_worker_v21.py').write_text(w)
e=(root/'tools/pv-dudect/window.py').read_text()
e=e.replace("assert r.returncode==0,'reservation refused; no scope started'", "assert r.returncode==0 and json.loads((O/'admission.json').read_text())['allowed'] is True,'reservation refused; no scope started'")
e=e.replace("str(B/'src/tools/pv-dudect/window_worker.py')", "str(B/'d294/window_worker_v21.py')")
(out/'window_v21.py').write_text(e)
