"""Source-only fixed ordinary-user diagnostic transport. Main disabled.
_reviewed_future is not called by this job; no allocation or SSH performed.
"""
import hashlib
import json
import os
from pathlib import Path
import resource
import selectors
import stat
import subprocess
import sys
import time

D=Path('/Users/dominic/ZK/.worktrees/cx-prover-rw/tools/prover-rw-20261023/final-native-gate')
PAYLOAD=D/'FinalNativeGate-admission-report-payload.txt'
PIN={'size': 10257, 'sha256': 'da8b1f52c34a012399c1fab602b12b31c3826f31f3544ef6df48827d25c3f290'}
CAPTURE=Path('/private/tmp/FinalNativeGate-admission-report-012-future')
ARGV=['/usr/bin/ssh','-T','-oBatchMode=yes','-oConnectTimeout=10','-oStrictHostKeyChecking=yes','-oClearAllForwardings=yes','-oForwardAgent=no','dombarker@100.108.41.90','/usr/bin/python3 -I -B -']
LIMIT=4*2**20


def stamp(s):
    return (s.st_dev,s.st_ino,s.st_mode,s.st_uid,s.st_gid,s.st_nlink,s.st_size,s.st_mtime_ns,s.st_ctime_ns)


def _reviewed_future():
    # Requires a later explicit lead allocation. Fixed absent capture; no retry,
    # overwrite, repair or second SSH. Charge is durable before Popen.
    start=time.monotonic();child=None;source=None;directory=None;outputs=[];receipt_stream=None
    errors=[];samples=[];total=0;exit_code=78;usage=None;actions=0
    if len(sys.argv)!=1:raise ValueError('no transport arguments')
    try:
        CAPTURE.mkdir(mode=0o700,exist_ok=False)
        owned=CAPTURE.lstat()
        if not stat.S_ISDIR(owned.st_mode) or owned.st_uid!=os.getuid() or stat.S_IMODE(owned.st_mode)!=0o700:
            raise ValueError('fixed capture current-owner0700 required')
        directory=os.open(CAPTURE,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW|os.O_CLOEXEC)
        if stamp(os.fstat(directory))!=stamp(owned):raise ValueError('capture open race')
        def exclusive(name):
            fd=os.open(name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW|os.O_CLOEXEC,0o600,dir_fd=directory)
            s=os.fstat(fd)
            if not stat.S_ISREG(s.st_mode) or s.st_uid!=os.getuid() or s.st_nlink!=1 or stat.S_IMODE(s.st_mode)!=0o600:
                os.close(fd);raise ValueError('fixed capture file0600 required')
            return os.fdopen(fd,'wb')
        receipt_stream=exclusive('receipt.json')
        source=os.open(PAYLOAD,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK|os.O_CLOEXEC)
        before=os.fstat(source)
        if not stat.S_ISREG(before.st_mode) or before.st_uid!=os.getuid() or before.st_nlink!=1 or before.st_mode&0o022 or before.st_size!=PIN['size'] or before.st_size>LIMIT:
            raise ValueError('fixed diagnostic source shape')
        raw=os.read(source,LIMIT+1)
        if len(raw)!=PIN['size'] or hashlib.sha256(raw).hexdigest()!=PIN['sha256'] or stamp(os.fstat(source))!=stamp(before):
            raise ValueError('fixed diagnostic source pin/drift')
        os.lseek(source,0,os.SEEK_SET)
        out=exclusive('stdout');outputs.append(out)
        err=exclusive('stderr');outputs.append(err)
        with exclusive('exclusive-future-charge.json') as charge:
            charge.write(json.dumps(dict(argv=ARGV,payload=PIN,SSH_charge=1,final_charge_authority=False)).encode())
            charge.flush();os.fsync(charge.fileno())
        os.fsync(directory)
        actions=1
        child=subprocess.Popen(ARGV,stdin=source,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            env=dict(HOME='/Users/dominic',PATH='/usr/bin:/bin',LANG='C.UTF-8'),close_fds=True)
        with selectors.DefaultSelector() as sel:
            for stream,dest in ((child.stdout,out),(child.stderr,err)):sel.register(stream,selectors.EVENT_READ,dest)
            while sel.get_map():
                if time.monotonic()-start>=20:raise TimeoutError('diagnostic local20s deadline')
                # Metadata only for our known local Python and SSH; no remote
                # process inventory. This is sampled, not a continuous cap.
                measured=subprocess.run(['/bin/ps','-o','rss=','-p',str(os.getpid())+','+str(child.pid)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=min(1,max(.001,20-(time.monotonic()-start))),check=True)
                rss=sum(int(x)*1024 for x in measured.stdout.split());samples.append(rss)
                if rss>=512*2**20:raise RuntimeError('sampled self+SSH512MiB bound')
                for key,_ in sel.select(.02):
                    data=os.read(key.fileobj.fileno(),65536)
                    if not data:sel.unregister(key.fileobj);continue
                    total+=len(data)
                    if total>LIMIT:raise ValueError('diagnostic combined4MiB bound')
                    key.data.write(data)
            while True:
                pid,status,usage=os.wait4(child.pid,os.WNOHANG)
                if pid:break
                if time.monotonic()-start>=20:raise TimeoutError('diagnostic SSH exit20s deadline')
                time.sleep(.02)
            child.returncode=os.waitstatus_to_exitcode(status);exit_code=child.returncode
        if stamp(os.fstat(source))!=stamp(before):raise ValueError('diagnostic source interval drift')
    except BaseException as exc:errors.append(repr(exc));exit_code=78
    finally:
        if child is not None:
            if child.returncode is None:
                child.kill();_,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status)
            child.stdout.close();child.stderr.close()
        if source is not None:os.close(source)
        for stream in outputs:
            try:stream.flush();os.fsync(stream.fileno())
            except OSError as exc:errors.append(repr(exc));exit_code=78
            finally:stream.close()
    # All outputs remain untrusted diagnostic data; no content execution,
    # receiver admission, repair, JSON authority or automatic publication.
    own=resource.getrusage(resource.RUSAGE_SELF);factor=1 if sys.platform=='darwin' else 1024
    receipt=dict(argv=ARGV,payload=PIN,exit=exit_code,errors=errors,wall_seconds=time.monotonic()-start,
        self_peak_rss_bytes=own.ru_maxrss*factor,child_peak_rss_bytes=usage.ru_maxrss*factor if usage else None,
        sampled_self_child_peak_rss_bytes=max(samples,default=0),swap=own.ru_nswap+(usage.ru_nswap if usage else 0),
        SSH_charged=actions,combined_bytes=total,print_axioms='N/A',kind='DiagnosticBytes',trusted=False,
        security_targets_established=False,remote_work_state='UNOBSERVED; no cleanup/identity inference')
    # Print only the bounded local receipt; stdout/stderr are retained in the
    # exclusive capture and never parsed or promoted by this transport.
    try:
        if receipt_stream is not None:
            receipt_stream.write(json.dumps(receipt,sort_keys=True).encode())
            receipt_stream.flush();os.fsync(receipt_stream.fileno())
        if directory is not None:os.fsync(directory)
    finally:
        try:
            if receipt_stream is not None:receipt_stream.close()
        finally:
            if directory is not None:os.close(directory)
    print(json.dumps(receipt,sort_keys=True));return exit_code


def main():
    print('FinalNativeGate admission report transport SOURCE disabled; lead review/new allocation required')
    return 78


if __name__=='__main__':raise SystemExit(main())
