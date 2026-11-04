"""Small optimized functional preflight, not final acceptance replay."""
from pathlib import Path
import subprocess,os,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');C=H/'src/tools/r1-cost-probe'
e=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'),RUSTFLAGS='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4')
c=['taskset','--cpu-list','0-3','cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features','r1p-check,aspis-r1-cost-probe/ct-host-prover','--bin','user_client','--bin','user_fixture_inputs','--bin','devnet_spend']
subprocess.run(c,cwd=C,env=e,check=True)
for name in ['user_client','devnet_spend','user_fixture_inputs']:
 p=H/'native-target/client'/name
 print(name,hashlib.sha256(p.read_bytes()).hexdigest(),p.stat().st_size,flush=True)
subprocess.run(['python3',str(H/'build-fixtures.py')],check=True)
O=H/'preflight';O.mkdir(exist_ok=False)
f=json.loads((H/'fixture-inputs.json').read_text());rows=[]
for fixture in ['transfer','withdrawal']:
 q=json.loads((H.parent/'codex-pv-c474-20261029/runtime-private-final/default'/fixture/'request.json').read_text());q.pop('note');q.update(lane_leaf_sets=f['lane_leaf_sets'],withdrawal_amount=250,proof_dir=str(O/(fixture+'-proof')))
 rfd,wfd=os.pipe();os.write(wfd,bytes.fromhex(f['records'][0 if fixture=='transfer' else 1]));os.close(wfd);q['wallet_bytes_fd']=rfd
 r=subprocess.run([H/'native-target/client/user_client'],input=json.dumps(q),capture_output=True,text=True,pass_fds=(rfd,),timeout=90);os.close(rfd)
 (O/(fixture+'-stdout.json')).write_text(r.stdout);(O/(fixture+'-stderr.txt')).write_text(r.stderr)
 rows.append(dict(fixture=fixture,exit=r.returncode,stderr=r.stderr))
 print(json.dumps(rows[-1]),flush=True)
 assert r.returncode==0
 v=json.loads(r.stdout);assert 'fixture' not in v and 'mask_audit' not in v
(O/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
