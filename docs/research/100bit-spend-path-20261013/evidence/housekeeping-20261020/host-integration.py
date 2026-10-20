import subprocess, pathlib, time, json, hashlib, os
root=pathlib.Path('/home/dombarker/project-offloads/codex-cx-housekeeping-20261020')
os.chdir(root/'src/crates/aspis-pool-wallet-v1')
receipt=root/'receipts'; receipt.mkdir(exist_ok=True)
for name,args in [('integration-default',['cargo','test','--release','--offline','--locked','-j','4','--test','*','--','--test-threads=1']),('integration-eight-lane',['cargo','test','--release','--offline','--locked','-j','4','--features','eight-lane-plumbing-v2','--test','*','--','--test-threads=1'])]:
    cmd=['/usr/bin/time','-v','-o',str(receipt/(name+'.time'))]+args
    start=time.time()
    with open(receipt/(name+'.log'),'w') as out: r=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
    (receipt/(name+'.json')).write_text(json.dumps(dict(command=args,exit=r.returncode,wall_seconds=time.time()-start,source_revision='74f689738905518e54f8532eaf368e333cefbf16',network='offline',expected_time='dependency compilation and wallet tests; no proof generation or elimination'),indent=2)+'\n')
    print(name,r.returncode,flush=True)
    if name=='lock' and r.returncode: break
