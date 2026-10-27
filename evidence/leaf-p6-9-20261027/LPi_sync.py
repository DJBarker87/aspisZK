"""Reconstruct LPi scratch harnesses from the committed patch; admit before upload."""
from pathlib import Path
import subprocess,json,shlex,tempfile
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-9-20261027'
def added_bytes(name):
 target='crates/aspis-r1-cost-probe/src/'+name
 active=False;out=[]
 for line in (E/'LPi_harness.patch').read_text().splitlines(True):
  if line.startswith('--- '):active=False
  elif line.startswith('+++ '):active=line.rstrip()=='+++ b/'+target
  elif active and line.startswith('+'):out.append(line[1:])
  elif active and line.startswith(' '):raise ValueError('Expected an added harness file')
 assert out,name
 return ''.join(out).encode()
def main():
 subprocess.run(['python3',str(E/'LPi_source_audit.py')],check=True)
 a='LPi_SYNC_'+str(len(list(E.glob('LPi_SYNC_*-reservation.json')))+1)
 r=subprocess.run(['ssh',H,f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{a}-barrier.log 2>&1'],capture_output=True,text=True)
 for tail in ['-reservation.json','-barrier.log']:subprocess.run(['scp','-q',H+':'+B+'/'+a+tail,str(E/(a+tail))],check=True)
 assert r.returncode==0 and json.loads((E/(a+'-reservation.json')).read_text())['allowed'],'STOP refused setup; no upload'
 with tempfile.TemporaryDirectory(prefix='LPi_harness_upload_') as td:
  for f in ['LPi_contracts.rs','LPi_verifier.rs']:
   p=Path(td)/f;p.write_bytes(added_bytes(f));subprocess.run(['scp','-q',str(p),H+':'+B+'/LPi_src/crates/aspis-r1-cost-probe/src/'+f],check=True)
 line='\n#[cfg(kani)] #[path="LPi_verifier.rs"] mod LPi_verifier;\n'
 script='from pathlib import Path; p=Path('+repr(B+'/LPi_src/crates/aspis-r1-cost-probe/src/verifier.rs')+'); s=p.read_text(); s=s.replace("\\n#[cfg(kani)] mod LPi_verifier;\\n", "\\n"); line='+repr(line)+'; p.write_text(s if line in s else s+line)'
 subprocess.run(['ssh',H,'python3 -c '+shlex.quote(script)],check=True)
if __name__=='__main__':main()
