#!/usr/bin/env python3
"""One job in this worker's private host workspace; collect exact receipts."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2]; D=R/'docs/research/100bit-spend-path-20261013'; E=D/'evidence/s2c-20261023'
HOST='dombarker@100.108.41.90'; H='/home/dombarker/project-offloads/codex-cx-s2c-20261023'
kind,num,target=sys.argv[1:4]; attempt=f'{kind}-{int(num):03d}'
assert kind in ['lean','kani'] and 0<int(num)<=(100 if kind=='lean' else 60)
assert not (E/attempt).exists(), 'Attempt already collected'
subprocess.run(['ssh',HOST,'mkdir','-p',H],check=True)
for f in ['run_host.py','reservation.py']:
 subprocess.run(['scp',str(Path(__file__).parent/f),HOST+':'+H+'/'+f],check=True)
if kind=='lean':
 sources=[target+'.lean','S2TrustedSdkBorrow.lean']
 for p in (D/'lean').glob('S2C_*.lean'):
  subprocess.run(['scp',str(p),HOST+':'+H+'/'+p.name],check=True)
 subprocess.run(['scp',str(D/'lean/S2TrustedSdkBorrow.lean'),HOST+':'+H+'/S2TrustedSdkBorrow.lean'],check=True)
 command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target+'.olean',target+'.lean']
 env={'LEAN_PATH':'.'}
 deps={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (D/'lean').glob('S2C_*.lean') if p.stem!=target}
 deps['S2TrustedSdkBorrow']=hashlib.sha256((D/'lean/S2TrustedSdkBorrow.lean').read_bytes()).hexdigest()
 subprocess.run(['ssh',HOST,f"cd {H} && printf 'name = \"s2c\"\nversion = \"0.1.0\"\n' > lakefile.toml && printf 'leanprover/lean4:v4.32.0\n' > lean-toolchain"],check=True)
 # Reuse only the explicitly hash-checked adopted trust object, in this workspace.
 subprocess.run(['ssh',HOST,f'cmp {H}/S2TrustedSdkBorrow.lean /home/dombarker/project-offloads/codex-cx-s2-trust-20261023/S2TrustedSdkBorrow.lean && cp /home/dombarker/project-offloads/codex-cx-s2-trust-20261023/S2TrustedSdkBorrow.olean {H}/'],check=True)
else:
 raise SystemExit('Kani configuration not yet installed')
cfg={'attempt':attempt,'kind':kind,'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'command':command,'sources':sources,'timeout':180,'deps_fingerprint':deps,'env':env}
(E/(attempt+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
subprocess.run(['scp',str(E/(attempt+'.json')),HOST+':'+H+'/'+attempt+'.json'],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 reservation.py {attempt}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 run_host.py {attempt}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+attempt,str(E/attempt)],check=True)
subprocess.run(['scp',HOST+':'+H+'/'+attempt+'-reservation.json',str(E)],check=True)
sys.exit(r.returncode)
