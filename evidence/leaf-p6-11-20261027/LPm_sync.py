"""Upload only this job's new module to the retained scratch, after admission."""
from pathlib import Path
import subprocess,json,shlex,tempfile
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-11-20261027'
a='LPm_SYNC_'+str(len(list(E.glob('LPm_SYNC_*-reservation.json')))+1)
r=subprocess.run(['ssh',H,f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1'],capture_output=True,text=True)
for tail in ['-reservation.json','-barrier.log']:subprocess.run(['scp','-q',H+':'+B+'/'+a+tail,str(E/(a+tail))],check=True)
assert r.returncode==0 and json.loads((E/(a+'-reservation.json')).read_text())['allowed'],'STOP refused sync'
r=subprocess.run(['ssh',H,f'mkdir -p {B}/LPm_tmp; test -e {B}/LPm_src || ln -s /home/dombarker/project-offloads/codex-cx-leaf-p6-9-20261027/LPi_src {B}/LPm_src'],check=True)
active=False;out=[]
for line in (E/'LPm_harness.patch').read_text().splitlines(True):
 if line.startswith('--- '):active=False
 elif line.startswith('+++ '):active=line.rstrip()=='+++ b/crates/aspis-r1-cost-probe/src/LPm_verifier.rs'
 elif active and line.startswith('+'):out.append(line[1:])
assert out
with tempfile.TemporaryDirectory(prefix='LPm_upload_') as td:
 p=Path(td)/'LPm_verifier.rs';p.write_text(''.join(out));subprocess.run(['scp','-q',str(p),H+':'+B+'/LPm_src/crates/aspis-r1-cost-probe/src/LPm_verifier.rs'],check=True)
line='\n#[cfg(kani)] #[path="LPm_verifier.rs"] mod LPm_verifier;\n'
script='from pathlib import Path; p=Path('+repr(B+'/LPm_src/crates/aspis-r1-cost-probe/src/verifier.rs')+'); s=p.read_text(); line='+repr(line)+'; p.write_text(s if line in s else s+line)'
subprocess.run(['ssh',H,'python3 -c '+shlex.quote(script)],check=True)
# A cfg(kani)-only child of canonical can observe the actual private caller ABI.
active=False;out=[]
for line in (E/'LPm_harness.patch').read_text().splitlines(True):
 if line.startswith('--- '):active=False
 elif line.startswith('+++ '):active=line.rstrip()=='+++ b/crates/aspis-r1-cost-probe/src/fast_pairing/canonical/LPm_pairing.rs'
 elif active and line.startswith('+'):out.append(line[1:])
if out:
 remote=B+'/LPm_src/crates/aspis-r1-cost-probe/src/fast_pairing/canonical'
 subprocess.run(['ssh',H,'mkdir -p '+remote],check=True)
 with tempfile.TemporaryDirectory(prefix='LPm_pairing_upload_') as td:
  p=Path(td)/'LPm_pairing.rs';p.write_text(''.join(out));subprocess.run(['scp','-q',str(p),H+':'+remote+'/LPm_pairing.rs'],check=True)
 marker='\n    #[cfg(kani)] #[path="LPm_pairing.rs"] mod LPm_pairing;\n'
 needle='\n}\n\n\nuse aspis_core::field'
 script='from pathlib import Path; p=Path('+repr(B+'/LPm_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs')+'); s=p.read_text(); marker='+repr(marker)+'; needle='+repr(needle)+'; assert marker in s or s.count(needle)==1; p.write_text(s if marker in s else s.replace(needle,marker+"}\\n\\n\\nuse aspis_core::field"))'
 subprocess.run(['ssh',H,'python3 -c '+shlex.quote(script)],check=True)
