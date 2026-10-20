#!/usr/bin/env python3
"""One focused module, a private object directory, and serialized local Lean."""
import os, sys, json, pathlib, subprocess, hashlib, time, datetime, re
root=pathlib.Path(__file__).resolve().parents[5]
packet=pathlib.Path(__file__).resolve().parent
module,attempt=sys.argv[1:3]
source=(root/sys.argv[3] if len(sys.argv)>3 else root/'docs/research/100bit-spend-path-20261013/lean'/f'{module}.lean')
prior=root/'docs/research/100bit-spend-path-20261013/evidence/sampler-rows-25-32-20261020/suffix-v3/command.json'
config=json.loads(prior.read_text())
leanpath=config.get('lean_path') or config.get('env',{}).get('LEAN_PATH')
if not leanpath:
    print(config); sys.exit(2)
obj=pathlib.Path('/tmp/cx-queryscan-20261020-objects');obj.mkdir(exist_ok=True)
dest=packet/attempt;dest.mkdir()
lock=pathlib.Path('/tmp/aspis-local-lean.lock.d')
while True:
    try: lock.mkdir(); break
    except FileExistsError: time.sleep(15)
try:
    while subprocess.run(['pgrep','-x','lean'],capture_output=True).returncode==0: time.sleep(60)
    argv=['/usr/bin/time','-l','/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M4400','-DElab.async=false','-o',str(obj/f'{module}.olean'),str(source)]
    env=os.environ.copy();env['LEAN_PATH']=str(obj)+':'+os.environ.get('QUERYSCAN_EXTRA_LEAN_PATH','')+':'+leanpath
    command={'argv':argv,'lean_path':env['LEAN_PATH'],'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    (dest/'command.json').write_text(json.dumps(command,indent=2)+'\n')
    (dest/'source.lean').write_bytes(source.read_bytes())
    start=time.monotonic()
    with (dest/'lean.log').open('w') as out, (dest/'time.log').open('w') as err:
        result=subprocess.run(argv,cwd=source.parent,env=env,stdout=out,stderr=err)
    logs=(dest/'lean.log').read_text(); timing=(dest/'time.log').read_text()
    receipt={'schema':'focused-extractor-proof-packet-v1','module':module,'attempt':attempt,**command,'exit':result.returncode,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':re.findall(r'(\d+)\s+maximum resident set size',timing),'swaps':re.findall(r'(\d+)\s+swaps',timing),'axioms':[l for l in logs.splitlines() if 'depends on axioms' in l or 'does not depend on any axioms' in l]}
    (dest/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(logs);print(timing);sys.exit(result.returncode)
finally: lock.rmdir()
