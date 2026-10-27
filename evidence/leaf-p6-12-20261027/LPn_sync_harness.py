from pathlib import Path
import subprocess,json,hashlib,tempfile
from LPn_harness_sources import sources
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-12-20261027'
# Only our prefixed harness is mutable. Other jobs' source is read only.
harnesses=sources(E/'LPn_harness.patch')
harnesses.update({p.name:p.read_bytes() for p in E.glob('LPn_*.rs')})
with tempfile.TemporaryDirectory(prefix='LPn_harness_') as td:
 for name,data in harnesses.items():
  local=Path(td)/name;local.write_bytes(data)
  subprocess.run(['scp','-q',str(local),H+':'+B+'/LPn_src/crates/aspis-r1-cost-probe/src/'+name],check=True)
code=f'''from pathlib import Path
import difflib,json,hashlib
B=Path('{B}');base=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-10-20261027/LPl_src');scratch=B/'LPn_src'
for harness in (scratch/'crates/aspis-r1-cost-probe/src').glob('LPn_*.rs'):
 parent=scratch/'crates/aspis-r1-cost-probe/src'/('verifier.rs' if harness.stem=='LPn_echeck' else 'r1_wire.rs' if harness.stem=='LPn_validate' else 'compact.rs')
 if ('mod '+harness.stem) not in parent.read_text():parent.write_text(parent.read_text()+'\\n#[cfg(kani)] mod '+harness.stem+' {{ include!("'+harness.name+'"); }}\\n')
a={{str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file()}}
b={{str(p.relative_to(scratch)):p for p in scratch.rglob('*') if p.is_file()}}
diff=''
for rel in sorted(b):
 old=a[rel].read_bytes() if rel in a else b'';new=b[rel].read_bytes()
 if old==new:continue
 diff+=''.join(difflib.unified_diff(old.decode().splitlines(True),new.decode().splitlines(True),fromfile='a/'+rel if rel in a else '/dev/null',tofile='b/'+rel))
(B/'LPn_harness.patch').write_text(diff)
print(json.dumps({{'sha256':hashlib.sha256(diff.encode()).hexdigest(),'bytes':len(diff.encode())}}))
'''
r=subprocess.run(['ssh',H,"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True)
print(r.stdout)
subprocess.run(['scp','-q',H+':'+B+'/LPn_harness.patch',str(E/'LPn_harness.patch')],check=True)

files=json.loads((E/'LPn_sources.json').read_text())
files=sorted(set(files+['crates/aspis-r1-cost-probe/src/'+p.name for p in map(Path,harnesses)]))
(E/'LPn_sources.json').write_text(json.dumps(files,indent=2)+'\n')
