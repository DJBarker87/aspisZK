import os, time, json, subprocess, pathlib, hashlib, datetime, sys
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
source=pathlib.Path('/tmp/query-s4-caller-v4-parent-cut-20261021/sources/Tx1OpsCut.lean')
outdir=pathlib.Path('/tmp/query-s4-caller-v4-parent-cut-20261021/objects')
ev=pathlib.Path('/tmp/query-s4-caller-v4-parent-cut-20261021/evidence/cut-v2')
outdir.mkdir(parents=True,exist_ok=True); ev.mkdir(parents=True,exist_ok=True)
lean='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
lp='/tmp/query-s4-caller-v4-parent-cut-20261021/objects:'+pathlib.Path('/tmp/root-s4-fullcaller-complete-path-20261021.txt').read_text().strip()
sha=lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
start=time.time(); deadline=start+55; owned=None
while time.time()<deadline:
    try:
        lock.mkdir()
        owned=lock.stat().st_ino
        break
    except FileExistsError:
        time.sleep(.25)
if owned is None:
    (ev/'acquire.json').write_text(json.dumps({'status':'LOCK_BUSY_TIMEOUT','wait_seconds':round(time.time()-start,3),'source_sha256':sha(source)},indent=2)+'\n')
    print('LOCK_BUSY_TIMEOUT'); sys.exit(75)
try:
    owner={'pid':os.getpid(),'target':'S4CallerV4Tx1OpsCut-query-v2','inode':owned,'source_sha256':sha(source),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (lock/'owner.json').write_text(json.dumps(owner,indent=2)+'\n')
    (ev/'preflight.json').write_text(json.dumps({'source':str(source),'source_sha256':sha(source),'compiler':lean,'compiler_version':subprocess.check_output([lean,'--version'],text=True).strip(),'lean_path_file':'/tmp/root-s4-fullcaller-complete-path-20261021.txt','lean_path_sha256':sha('/tmp/root-s4-fullcaller-complete-path-20261021.txt'),'lock_inode':owned,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd='/Users/dominic/ZK',text=True).strip()},indent=2)+'\n')
    cmd=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+lp,lean,'-j1','-M','4400','-R',str(source.parent),'-o',str(outdir/'Tx1OpsCutQuery.olean'),str(source)]
    with (ev/'lean.log').open('w') as f:
        p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    receipt={'exit_code':p.returncode,'elapsed_seconds':round(time.time()-start,3),'source_sha256':sha(source),'object_sha256':sha(outdir/'Tx1OpsCutQuery.olean') if (outdir/'Tx1OpsCutQuery.olean').exists() else None,'command':cmd[0:7]+['<LEAN_PATH>']+cmd[8:]}
    (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))
    sys.exit(p.returncode)
finally:
    try:
        if lock.stat().st_ino==owned:
            (lock/'owner.json').unlink(missing_ok=True)
            lock.rmdir()
    except FileNotFoundError:
        pass
