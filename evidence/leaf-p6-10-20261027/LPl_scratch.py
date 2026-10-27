from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-10-20261027'
def ssh(s):return subprocess.run(['ssh',H,s],check=True,text=True,capture_output=True)
# A single private scratch tree for this job; inherited source is read only.
ssh(f'test -e {B}/LPl_src || cp -a /home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027/LPh_src {B}/LPl_src')
subprocess.run(['scp','-q',str(E/'LPl_echeck.rs'),H+':'+B+'/LPl_src/crates/aspis-r1-cost-probe/src/LPl_echeck.rs'],check=True)
code=f'''from pathlib import Path
import hashlib,json,difflib
B=Path('{B}');base=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027/LPh_src');scratch=B/'LPl_src'
p=scratch/'crates/aspis-r1-cost-probe/src/verifier.rs'
if 'mod LPl_echeck' not in p.read_text():p.write_text(p.read_text()+'\\n#[cfg(kani)] mod LPl_echeck {{ include!("LPl_echeck.rs"); }}\\n')
a={{str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file()}}
b={{str(p.relative_to(scratch)):p for p in scratch.rglob('*') if p.is_file()}}
diff=''
for rel in sorted(b):
 old=a[rel].read_bytes() if rel in a else b''
 new=b[rel].read_bytes()
 if old==new:continue
 old=old.decode();new=new.decode()
 if old!=new:diff+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+rel if rel in a else '/dev/null',tofile='b/'+rel))
(B/'LPl_harness.patch').write_text(diff)
print(json.dumps({{'base':str(base),'scratch':str(scratch),'manifest':{{rel:hashlib.sha256(p.read_bytes()).hexdigest() for rel,p in b.items()}},'base_manifest':{{rel:hashlib.sha256(p.read_bytes()).hexdigest() for rel,p in a.items()}},'added':[rel for rel in b if rel not in a],'changed':[rel for rel in a if a[rel].read_bytes()!=b[rel].read_bytes()]}}))
'''
r=ssh("python3 - <<'REMOTE'\n"+code+'\nREMOTE');x=json.loads(r.stdout)
(E/'LPl_source-provenance.json').write_text(json.dumps(x,indent=2)+'\n')
subprocess.run(['scp','-q',H+':'+B+'/LPl_harness.patch',str(E/'LPl_harness.patch')],check=True)
sources=sorted(set(json.loads(Path('evidence/leaf-p6-8-20261027/LPh_sources.json').read_text())+['crates/aspis-r1-cost-probe/src/LPl_echeck.rs']))
(E/'LPl_sources.json').write_text(json.dumps(sources,indent=2)+'\n')
print('Private source tree:',len(x['manifest']),'files; changed',x['changed'],'added',x['added'])
