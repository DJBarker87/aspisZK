#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, os, re, subprocess, time
P = Path(__file__).resolve().parents[1]
REPO = P.parents[4]
SRC = P / 'sources/S4V10InstalledToLimbsSlotV1.lean'
OBJ = Path('/tmp/s4-v10-installed-to-limbs-slot-v1/objects/S4V10InstalledToLimbsSlotV1.olean')
OBJ.parent.mkdir(parents=True, exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
source_pin = 'docs/research/100bit-spend-path-20261013/evidence/s4-v10-to-limbs-source-bridge-v1-20261021/sources/lean/S4V10ToLimbsCarrierBridgeV1.lean'
head_pin = 'docs/research/100bit-spend-path-20261013/evidence/s4-current-head-term-forward-root-v1-20261021/sources/S4CurrentHeadTermForwardRootV1.lean'
bridge_obj = Path('/tmp/s4-v10-wide-to-limbs-bridge-v1/S4V10ToLimbsCarrierBridgeV1.olean')
head_obj = Path('/tmp/root-s4-current-head-term-forward-v1-20261021/objects/S4CurrentHeadTermForwardRootV1.olean')
compiler = Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
cache = Path('/tmp/root-s4-installed-callback-value-cache-20261021')
bridge = Path('/tmp/s4-v10-wide-to-limbs-bridge-v1')
maproot = Path('/tmp/s4-v10-transparent-carrier-map-objects')
headlp = json.loads((REPO/'docs/research/100bit-spend-path-20261013/evidence/s4-current-head-term-forward-root-v1-20261021/evidence/command.json').read_text())['argv']
headlp = next(x[10:] for x in headlp if x.startswith('LEAN_PATH='))
overlay = Path('/tmp/s4-to-limbs-current-namespace-overlay')
resolved = []
for p in sorted((overlay/'AspisR1FastDotsCurrent').glob('*.olean')):
    resolved.append({'module_path':str(p.relative_to(overlay)), 'resolved_path':str(p.resolve()), 'sha256':sha(p.resolve())})
(P/'receipts/namespace-overlay.json').write_text(json.dumps({'schema':'lean-module-namespace-overlay-v1','entries':resolved},indent=2)+'\n')
lp = ':'.join([str(overlay),str(bridge),str(maproot),str(maproot/'generated'),str(Path('/tmp/root-s4-current-head-term-forward-v1-20261021/objects')),headlp])
lock = Path('/tmp/aspis-local-lean.lock.d')
start_wait = time.monotonic()
while True:
    try: lock.mkdir(); break
    except FileExistsError:
        if time.monotonic()-start_wait > 55: raise SystemExit('mutex timeout; no Lean launched')
        time.sleep(.25)
inode = lock.stat().st_ino
(lock/'owner.json').write_text(json.dumps({'pid':os.getpid(),'inode':inode,'target':'S4V10InstalledToLimbsSlotV1'}))
try:
    live=[]
    for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines():
        parts=line.strip().split(None,1)
        if len(parts)==2 and Path(parts[1]).name=='lean': live.append(int(parts[0]))
    if live: raise SystemExit('live Lean process excludes launch: '+str(live))
    rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
    direct={
      'S4V10ToLimbsCarrierBridgeV1':{'source_path':source_pin,'source_sha256':sha(REPO/source_pin),'object_path':str(bridge_obj),'object_sha256':sha(bridge_obj)},
      'S4CurrentHeadTermForwardRootV1':{'source_path':head_pin,'source_sha256':sha(REPO/head_pin),'object_path':str(head_obj),'object_sha256':sha(head_obj)},
    }
    cmd=['/usr/bin/time','-l','-o',str(P/'receipts/time.log'),str(compiler),'-j1','-M','4400','-R',str(SRC.parent),'-o',str(OBJ),str(SRC)]
    pre={'schema':'focused-lean-preflight-v1','target':'S4V10InstalledToLimbsSlotV1','source_sha256':sha(SRC),'launch_revision':rev,'compiler':str(compiler),'compiler_sha256':sha(compiler),'lean_path':lp,'direct_imports':direct,'namespace_overlay':'receipts/namespace-overlay.json','threads':1,'lean_memory_mb':4400,'no_dependency_builds':True}
    (P/'receipts/preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
    (P/'receipts/command.json').write_text(json.dumps({'argv':cmd,'cwd':str(SRC.parent),'env':{'LEAN_PATH':lp},'lock_inode':inode},indent=2)+'\n')
    t=time.monotonic(); result=subprocess.run(cmd,cwd=SRC.parent,env={**os.environ,'LEAN_PATH':lp},capture_output=True,text=True,timeout=120)
    log=result.stdout+result.stderr
    (P/'receipts/compile.log').write_text(log)
    time_text=(P/'receipts/time.log').read_text()
    rss=re.search(r'(\d+)\s+maximum resident set size',time_text)
    swaps=re.search(r'(\d+)\s+swaps',time_text)
    receipt={'schema':'focused-lean-receipt-v1','target':'S4V10InstalledToLimbsSlotV1','exit_status':result.returncode,'wall_seconds':round(time.monotonic()-t,3),'peak_rss_bytes':int(rss.group(1)) if rss else None,'swap_bytes':int(swaps.group(1)) if swaps else None,'source_sha256':sha(SRC),'object_sha256':sha(OBJ) if OBJ.is_file() else None,'launch_revision':rev,'compiler':str(compiler),'compiler_sha256':sha(compiler),'direct_imports':direct,'axioms':['propext','Classical.choice','Quot.sound'] if 'depends on axioms: [propext,' in log else None}
    (P/'receipts/receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2)); print(log)
    raise SystemExit(result.returncode)
finally:
    if lock.exists() and lock.stat().st_ino==inode:
        owner=json.loads((lock/'owner.json').read_text())
        if owner.get('pid')==os.getpid() and owner.get('inode')==inode:
            (lock/'owner.json').unlink(); lock.rmdir()
