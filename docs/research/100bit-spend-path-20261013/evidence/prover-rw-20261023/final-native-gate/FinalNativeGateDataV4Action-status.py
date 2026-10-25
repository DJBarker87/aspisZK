"""One conditional read-only status query; no log reads or workload actions."""
import datetime,json,os,pathlib,resource,selectors,subprocess,time
E=pathlib.Path(__file__).resolve().parent
P='FinalNativeGateDataV4Action-'
REMOTE='/usr/bin/env -i HOME=/home/dombarker USER=dombarker LOGNAME=dombarker PATH=/usr/bin:/bin LANG=C.UTF-8 LC_ALL=C.UTF-8 XDG_RUNTIME_DIR=/run/user/1000 DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus /usr/bin/timeout 10 /usr/bin/systemctl --user show FinalNativeGate-pin-setup.scope --no-pager --property=LoadState,ActiveState,SubState,InvocationID,ActiveEnterTimestampMonotonic,ControlGroup'
ARGV=['/usr/bin/ssh','-T','-oBatchMode=yes','-oConnectTimeout=10','-oStrictHostKeyChecking=yes','-oClearAllForwardings=yes','-oForwardAgent=no','dombarker@100.108.41.90',REMOTE]
def main():
    with (E/(P+'status-charge.json')).open('x') as f:
        json.dump(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),conditional_new=1,main_new=1,argv=ARGV,reason='primary missing both terminal records; summary permission rejection; setup_exit78',print_axioms='N/A'),f,indent=2);f.flush();os.fsync(f.fileno())
    start=time.monotonic();errors=[];total=0;samples=[]
    with (E/(P+'status.stdout')).open('xb') as out,(E/(P+'status.stderr')).open('xb') as err:
        child=subprocess.Popen(ARGV,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=dict(HOME='/Users/dominic',PATH='/usr/bin:/bin',LANG='C.UTF-8'),close_fds=True)
        try:
            with selectors.DefaultSelector() as sel:
                for stream,dest in ((child.stdout,out),(child.stderr,err)):sel.register(stream,selectors.EVENT_READ,dest)
                while sel.get_map():
                    if time.monotonic()-start>20:raise TimeoutError('conditional20s local bound')
                    r=subprocess.run(['/bin/ps','-p',str(os.getpid())+','+str(child.pid),'-o','pid=,ppid=,rss='],capture_output=True,text=True)
                    samples.append(dict(elapsed=time.monotonic()-start,rows=r.stdout))
                    for key,_ in sel.select(.05):
                        raw=os.read(key.fileobj.fileno(),65536)
                        if not raw:sel.unregister(key.fileobj);continue
                        total+=len(raw)
                        if total>4*2**20:raise ValueError('combined4MiB summary bound')
                        key.data.write(raw)
                child.wait(timeout=max(.001,20-(time.monotonic()-start)))
        except BaseException as exc:errors.append(repr(exc))
        finally:
            if child.poll() is None:child.kill()
            child.wait();child.stdout.close();child.stderr.close()
            out.flush();err.flush();os.fsync(out.fileno());os.fsync(err.fileno())
    u=resource.getrusage(resource.RUSAGE_SELF);c=resource.getrusage(resource.RUSAGE_CHILDREN)
    with (E/(P+'status-receipt.json')).open('x') as f:
        json.dump(dict(argv=ARGV,pid=child.pid,exit=child.returncode,errors=errors,wall_seconds=time.monotonic()-start,peak_self_rss_bytes=u.ru_maxrss,peak_child_rss_bytes=c.ru_maxrss,swap_self=u.ru_nswap,swap_children=c.ru_nswap,samples=samples,public_bytes=total,utc_end=datetime.datetime.now(datetime.timezone.utc).isoformat(),print_axioms='N/A',known_uid1000='reused historical metadata, not guessed',closure='assess exact returned unit properties; no second poll'),f,indent=2)
    print(json.dumps(dict(exit=child.returncode,errors=errors)))
if __name__=='__main__':main()
