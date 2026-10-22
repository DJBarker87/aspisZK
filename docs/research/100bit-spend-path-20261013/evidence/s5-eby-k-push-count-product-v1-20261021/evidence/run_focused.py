import hashlib,json,os,pathlib,subprocess,time,sys
src=pathlib.Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/lean-candidates/s5-current-repin-20261020/eby-k-push-count-product-v1/EbyKPushCountInvariantProductUpdateV1.lean')
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
lean='/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
out=pathlib.Path('/tmp/EbyKPushCountInvariantProductUpdateV1-current.olean')
log=pathlib.Path('/tmp/EbyKPushCountInvariantProductUpdateV1-current.log')
timefile=pathlib.Path('/tmp/EbyKPushCountInvariantProductUpdateV1-current.time.log')
roots=['/tmp/eby-k-push-totality-v2-objects','/tmp/qraw-v16-objects','/tmp/s5-qraw-totality-v1-objects','/tmp/prepared-local-warm-cache-20261020','/tmp/s4-p6-formatter-repair-closure','/Users/dominic/ZK/AspisFormal/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/mathlib/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/batteries/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/aesop/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/Qq/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/Cli/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/proofwidgets/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/importGraph/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/LeanSearchClient/.lake/build/lib/lean','/Users/dominic/ZK/AspisFormal/.lake/packages/plausible/.lake/build/lib/lean']
roots=[x for x in roots if pathlib.Path(x).exists()]
for module in ['EbyKPushTotalityV1.olean','FinishDotCountBoundV3.olean']:
    if not any((pathlib.Path(r)/module).exists() for r in roots): print('MISSING_MODULE',module); sys.exit(2)
acquired=False
started=time.monotonic()
while time.monotonic()-started < 55:
    p=subprocess.run(['ps','-axo','pid,comm'],capture_output=True,text=True)
    live=[x for x in p.stdout.splitlines()[1:] if x.split() and x.split()[-1] in ('lean','lake')]
    if live:
        time.sleep(.25); continue
    try:
        lock.mkdir(); acquired=True
    except FileExistsError:
        time.sleep(.25); continue
    inode=lock.stat().st_ino
    owner={'pid':os.getpid(),'target':'EbyKPushCountInvariantProductUpdateV1-current','inode':inode,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
    (lock/'owner.json').write_text(json.dumps(owner,sort_keys=True)+'\n')
    p=subprocess.run(['ps','-axo','pid,comm'],capture_output=True,text=True)
    live=[x for x in p.stdout.splitlines()[1:] if x.split() and x.split()[-1] in ('lean','lake')]
    if live:
        try:
            if lock.stat().st_ino==inode:
                current=json.loads((lock/'owner.json').read_text())
                if current.get('pid')==os.getpid() and current.get('inode')==inode:
                    (lock/'owner.json').unlink(); lock.rmdir()
        except FileNotFoundError: pass
        acquired=False; time.sleep(.25); continue
    break
if not acquired: print('LOCK_OR_LEAN_BUSY_TIMEOUT'); sys.exit(3)
try:
    # Do not start Lean if an unrelated Lean/Lake process appeared before lock acquisition.
    p=subprocess.run(['ps','-axo','pid,comm'],capture_output=True,text=True)
    live=[x for x in p.stdout.splitlines()[1:] if x.split() and x.split()[-1] in ('lean','lake')]
    if live: print('EXTERNAL_LEAN',live); sys.exit(4)
    git=subprocess.check_output(['git','-C','/Users/dominic/ZK','rev-parse','HEAD'],text=True).strip()
    sha=hashlib.sha256(src.read_bytes()).hexdigest()
    meta={'source_sha256':sha,'git_head':git,'lean_path':lean,'lean_sha256':hashlib.sha256(pathlib.Path(lean).read_bytes()).hexdigest(),'argv':['lean','-j1','-M4400','-o',str(out),str(src)],'lean_path_roots':roots,'launch_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
    pathlib.Path('/tmp/EbyKPushCountInvariantProductUpdateV1-current.launch.json').write_text(json.dumps(meta,indent=2)+'\n')
    env=os.environ.copy(); env['LEAN_PATH']=':'.join(roots)
    with log.open('w') as f:
        res=subprocess.run(['/usr/bin/time','-l','-o',str(timefile),lean,'-j1','-M4400','-o',str(out),str(src)],env=env,stdout=f,stderr=subprocess.STDOUT,timeout=240)
    meta['exit_status']=res.returncode; meta['source_sha256_after']=hashlib.sha256(src.read_bytes()).hexdigest(); meta['object_sha256']=hashlib.sha256(out.read_bytes()).hexdigest() if out.exists() else None
    pathlib.Path('/tmp/EbyKPushCountInvariantProductUpdateV1-current.receipt.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(meta,indent=2)); print('LOG',log); print('TIME',timefile)
finally:
    try:
        if lock.stat().st_ino==inode:
            current=json.loads((lock/'owner.json').read_text()) if (lock/'owner.json').exists() else {}
            if current.get('pid')==os.getpid() and current.get('inode')==inode:
                (lock/'owner.json').unlink(missing_ok=True); lock.rmdir()
    except FileNotFoundError: pass
