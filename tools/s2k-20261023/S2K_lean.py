"""One new module per attempt, private host objects, inherited pinned cache."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2k-20261023';T=Path(__file__).parent
H='/home/dombarker/project-offloads/codex-cx-s2k-20261023';HOST='dombarker@100.108.41.90'
n=int(sys.argv[1]);target=sys.argv[2];assert 77<=n<=176 and target.startswith('S2K_');a=f'lean-{n:03d}';assert not (E/a).exists()
p=D/'lean'/(target+'.lean');subprocess.run(['scp',str(p),HOST+':'+H+'/'+p.name],check=True)
# Existing merged overlay is read only and carries all split-olean companions.
prior=D/'evidence/s2i-20261023/lean-011/receipt.json';old=json.loads(prior.read_text())
paths=old['env']['LEAN_PATH'];x=dict(attempt=a,kind='lean',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target+'.olean',target+'.lean'],sources=[p.name],timeout=180,env={'LEAN_PATH':H+':'+paths},deps_fingerprint={'inherited_receipt_sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),'inherited_selected_overlay_sha256':old['deps_fingerprint']['selected_overlay_sha256'],'scope':'focused cached dependency compile; selected imported objects independently hashed before run'},expected_time='symbolic list serialization induction, cached imports; no concrete recurrence or full manifest')
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(E/(a+'.json')),HOST+':'+H+'/'+a+'.json'],check=True)
for f in ['S2K_run_host.py','S2K_reservation.py','S2K_lean_host.py']:subprocess.run(['scp',str(T/f),HOST+':'+H+'/'+f],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2K_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2K_lean_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True);subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True);sys.exit(r.returncode)
