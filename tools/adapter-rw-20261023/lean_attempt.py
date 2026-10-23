"""Private one-module capped host attempts; preserve receipts and never retry unchanged inputs."""
from pathlib import Path
import json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/adapter-rw-20261023';T=Path(__file__).parent
H='/home/dombarker/project-offloads/codex-cx-adapter-rw-20261023';HOST='dombarker@100.108.41.90'
n=int(sys.argv[1]);target=sys.argv[2];assert 2<=n<=100 and target.startswith('AdapterRw');a=f'lean-{n:03d}';assert not (E/a).exists()
p=D/'lean'/(target+'.lean')
old=json.loads((D/'evidence/s2i-20261023/lean-011/receipt.json').read_text())
paths=old['env']['LEAN_PATH']
x=dict(attempt=a,kind='lean',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target+'.olean',target+'.lean'],sources=[p.name],timeout=180,env={'LEAN_PATH':H+':'+paths},deps_fingerprint={'inherited_receipt_sha256':hashlib.sha256((D/'evidence/s2i-20261023/lean-011/receipt.json').read_bytes()).hexdigest(),'scope':'selected direct objects and companions pinned; inherited S2I union closure retained'},source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=R,text=True)),expected_time='focused cached extraction/proof compilation; no dependency build or arithmetic aggregation')
for f in ['run_host.py','reservation.py','lean_host.py']:subprocess.run(['scp',str(T/f),HOST+':'+H+'/'+f],check=True)
subprocess.run(['scp',str(p),HOST+':'+H+'/'+p.name],check=True)
q=T/(a+'.json');q.write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(q),HOST+':'+H+'/'+q.name],check=True)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 lean_host.py {a}.json'])
subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True)
subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True)
sys.exit(r.returncode)
