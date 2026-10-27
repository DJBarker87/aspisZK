from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-10-20261027'
# Only our prefixed harness is mutable. Other jobs' source is read only.
for local in E.glob('LPl_*.rs'):
 target='verifier.rs' if local.name=='LPl_echeck.rs' else 'compact.rs'
 subprocess.run(['scp','-q',str(local),H+':'+B+'/LPl_src/crates/aspis-r1-cost-probe/src/'+local.name],check=True)
code=f'''from pathlib import Path
import difflib,json,hashlib
B=Path('{B}');base=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027/LPh_src');scratch=B/'LPl_src'
a={{str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file()}}
b={{str(p.relative_to(scratch)):p for p in scratch.rglob('*') if p.is_file()}}
diff=''
for rel in sorted(b):
 old=a[rel].read_bytes() if rel in a else b'';new=b[rel].read_bytes()
 if old==new:continue
 diff+=''.join(difflib.unified_diff(old.decode().splitlines(True),new.decode().splitlines(True),fromfile='a/'+rel if rel in a else '/dev/null',tofile='b/'+rel))
(B/'LPl_harness.patch').write_text(diff)
print(json.dumps({{'sha256':hashlib.sha256(diff.encode()).hexdigest(),'bytes':len(diff.encode())}}))
'''
r=subprocess.run(['ssh',H,"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True)
print(r.stdout)
subprocess.run(['scp','-q',H+':'+B+'/LPl_harness.patch',str(E/'LPl_harness.patch')],check=True)
