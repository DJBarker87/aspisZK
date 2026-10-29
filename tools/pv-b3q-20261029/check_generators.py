"""Reproduce generated fixtures in isolated scratch and compare exact text."""
from pathlib import Path
import subprocess,tempfile,shutil,json,hashlib
root=Path.cwd();T=root/'tools/pv-b3q-20261029';D=root/'evidence/pv-b3q-20261029';checked=[]
with tempfile.TemporaryDirectory(prefix='generator-check-',dir=T)as td:
 w=Path(td);(w/'tools/pv-b3p6-20261028').mkdir(parents=True);(w/'tools/pv-b3p6-20261028/v244').symlink_to(root/'tools/pv-b3p6-20261028/v244',target_is_directory=True)
 (w/'evidence/pv-b3q-20261029/lean').mkdir(parents=True);(w/'tools/pv-b3q-20261029').mkdir()
 for name in ['d188_fixtures.py','d188_more.py','std_partial.py']:
  shutil.copy2(T/name,w/'tools/pv-b3q-20261029'/name)
 # Cargo.lock and canonical native main precede the observation-only suffix.
 (w/'tools/pv-b3p6-20261028/v244-safe13').mkdir()
 for f in ['Cargo.toml','Cargo.lock']:
  shutil.copy2(root/'tools/pv-b3p6-20261028/v244-safe13'/f,w/'tools/pv-b3p6-20261028/v244-safe13'/f)
 subprocess.run(['python3','tools/pv-b3q-20261029/d188_fixtures.py'],cwd=w,check=True,stdout=subprocess.DEVNULL)
 (w/'tools/pv-b3q-20261029/d188/main.rs').write_bytes(subprocess.check_output(['git','show','97d368ff45:tools/pv-b3q-20261029/d188/main.rs']))
 subprocess.run(['python3','tools/pv-b3q-20261029/d188_more.py'],cwd=w,check=True,stdout=subprocess.DEVNULL)
 subprocess.run(['python3','tools/pv-b3q-20261029/std_partial.py'],cwd=w,check=True,stdout=subprocess.DEVNULL)
 for p in sorted((w/'evidence/pv-b3q-20261029/lean').glob('*.lean')):
  actual=D/'lean'/p.name;assert actual.read_bytes()==p.read_bytes(),actual
  checked.append(dict(path=str(actual.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 for name in ['reference_terminal.rs','reference_copy_terminal.rs','reference_poseidon.rs','main.rs']:
  p=w/'tools/pv-b3q-20261029/d188'/name;q=T/'d188'/name;assert p.read_bytes()==q.read_bytes(),q
  checked.append(dict(path=str(q.relative_to(root)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(D/'generator-checks.json').write_text(json.dumps(dict(checked=checked,status='exact regeneration; isolated scratch; no live proof inputs overwritten'),indent=2)+'\n')
print(json.dumps(dict(files=len(checked),status='pass')))
