#!/usr/bin/env python3
"""Run one cost-only command on nuc with a fresh receipt and 4G/6G/no-swap."""
import hashlib,json,os,pathlib,socket,subprocess,sys
assert socket.gethostname().split('.')[0]=='nuc'
root=pathlib.Path('/home/dombarker/project-offloads/aspis-100bit-path-20261013')
out=root/'results/gr1-cost-20261013';out.mkdir(exist_ok=True)
label=sys.argv[1];cwd=pathlib.Path(sys.argv[2]);command=sys.argv[3:]
assert command and '/' not in label and not (out/(label+'.json')).exists()
reservations=[]
for line in subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True).splitlines():
 unit=line.split()[0]
 if unit=='init.scope':continue
 v=dict(x.split('=',1) for x in subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryMax','-p','MemoryCurrent'],text=True).splitlines())
 assert v['MemoryMax'].isdigit(),(unit,v)
 reservations.append(dict(unit=unit,**v))
assert sum(int(x['MemoryMax']) for x in reservations)+6*2**30<=50*2**30
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
paths=[pathlib.Path(command[0])]+[(cwd/x) for x in command[1:] if (cwd/x).is_file()]
paths=[p for p in paths if p.is_file()]
hashes={str(p.resolve()):sha(p) for p in paths}
(out/(label+'-inputs.json')).write_text(json.dumps(dict(command=command,cwd=str(cwd),active_scopes=reservations,sha256=hashes),indent=2)+'\n')
env=dict(os.environ,ASPIS_SOURCE_REVISION='628054cd4+gr1-cost-20261013+frozen-v3b-a810048410e72612d757353f53555b8c586115a13b519060989ed6ab533733f2',CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-r1-p2-20261010/target',CARGO_BUILD_JOBS='2')
cmd=['systemd-run','--user','--scope','--unit=aspis-gr1-'+label,'-p','MemoryHigh=4G','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=128','python3',str(root/'scripts/v8_state_only_cu_record.py'),str(out/label)]+command
r=subprocess.run(cmd,cwd=cwd,env=env)
assert all(sha(p)==s for p,s in hashes.items()),'input changed during run'
sys.exit(r.returncode)
