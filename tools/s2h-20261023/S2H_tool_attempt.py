from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parents[2];T=Path(__file__).parent;D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2h-20261023'
HOST='dombarker@100.108.41.90';H='/home/dombarker/project-offloads/codex-cx-s2h-20261023';a='audit-001'
assert not (E/a).exists()
for f in ['S2H_toolcheck.py','S2H_run_host.py','S2H_reservation.py']:
 subprocess.run(['scp',str(T/f),HOST+':'+H+'/'+f],check=True,stdout=subprocess.DEVNULL)
x={'attempt':a,'kind':'audit','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'command':['python3','S2H_toolcheck.py'],'sources':['S2H_toolcheck.py','S2H_run_host.py','S2H_reservation.py'],'timeout':180,'deps_fingerprint':'Revalidate inherited 2433-object Lean sysroot manifest and compiler hashes; no proof/compile/rebuild','expected_time':'read-only hashing of pinned cache/tool files'}
p=E/(a+'.json');p.write_text(json.dumps(x,indent=2)+'\n');subprocess.run(['scp',str(p),HOST+':'+H+'/'+p.name],check=True,stdout=subprocess.DEVNULL)
r=subprocess.run(['ssh',HOST,f'cd {H} && python3 S2H_reservation.py {a}-reservation.json && systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2H_run_host.py {a}.json'])
for remote,local in [(a,E/a),(a+'-reservation.json',E/(a+'-reservation.json')),('S2H-tool-pins.json',E/'S2H-tool-pins.json')]:
 subprocess.run(['scp','-r',HOST+':'+H+'/'+remote,str(local)],check=True,stdout=subprocess.DEVNULL)
sys.exit(r.returncode)
