from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2g-20261023'
H='/home/dombarker/project-offloads/codex-cx-s2g-20261023';HOST='dombarker@100.108.41.90'
n=int(sys.argv[1]);target=sys.argv[2];assert 1<=n<=100 and target.startswith('S2G_')
a=f'lean-{n:03d}';assert not (E/a).exists()
prior=json.loads((D/'evidence/s2e-20261023/lean-023/receipt.json').read_text())
paths=prior['env']['LEAN_PATH'].split(':');base='/home/dombarker/project-offloads/codex-cx-s2e-20261023'
paths=[base if p=='.' else base+'/'+p if not p.startswith('/') else p for p in paths]
paths += ['/home/dombarker/project-offloads/codex-cx-s2b-20261023/lead-overlay','/home/dombarker/project-offloads/codex-cx-s2b-20261023/objects']
paths.insert(0,'/home/dombarker/project-offloads/codex-cx-import-union-20261022/objects')
subprocess.run(['ssh',HOST,'mkdir','-p',H],check=True)
sources=sorted((D/'lean').glob('S2G_*.lean'))
for p in sources:subprocess.run(['scp',str(p),HOST+':'+H+'/'+p.name],check=True,stdout=subprocess.DEVNULL)
for src,dst in [(R/'tools/s2e-20261023/S2E_run_host.py','S2G_run_host.py'),(R/'tools/s2e-20261023/S2E_reservation.py','S2G_reservation.py'),(Path(__file__).parent/'S2G_pins.py','S2G_pins.py')]:subprocess.run(['scp',str(src),HOST+':'+H+'/'+dst],check=True,stdout=subprocess.DEVNULL)
cfg=dict(attempt=a,kind='lean',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),command=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M4400','-DElab.async=false','-o',target+'.olean',target+'.lean'],sources=[p.name for p in sources],timeout=180,env={'LEAN_PATH':H+':'+':'.join(paths)},expected_time='focused symbolic child-contract elaboration from cached dependencies; no arithmetic generation')
(E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');subprocess.run(['scp',str(E/(a+'.json')),HOST+':'+H+'/'+a+'.json'],check=True,stdout=subprocess.DEVNULL)
command=f'cd {H} && python3 S2G_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2G_pins.py {a}.json'
r=subprocess.run(['ssh',HOST,command]);subprocess.run(['scp','-r',HOST+':'+H+'/'+a,str(E/a)],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['scp',HOST+':'+H+'/'+a+'-reservation.json',str(E)],check=True,stdout=subprocess.DEVNULL)
subprocess.run([sys.executable,str(Path(__file__).parent/'S2G_inventory.py')],check=True)
sys.exit(r.returncode)
