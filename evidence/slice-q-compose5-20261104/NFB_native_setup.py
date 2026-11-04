from NFB_remote import *
import hashlib,json,subprocess
R=E.parent.parent;a='NFB_NATIVE_SETUP';admit(a)
files={f:subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f],cwd=R,text=True) for f in ['crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/lib.rs','crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/fast_dots.rs','Cargo.lock']}
files['crates/aspis-r1-cost-probe/src/verifier.rs']+='\n#[cfg(kani)]\nmod NFB_geometry;\n'
files['crates/aspis-r1-cost-probe/src/verifier/NFB_geometry.rs']=(E/'NFB_geometry.rs.txt').read_text()
code=f'''from pathlib import Path
import shutil,json,hashlib,subprocess
b=Path({B!r});s=b/'NFB_src';old=b.parent/'codex-cx-slice-q-compose4-20261104/NEW_src'
assert not s.exists()
shutil.copytree(old,s,symlinks=True,ignore=shutil.ignore_patterns('target','.git'))
for name,source in json.loads({json.dumps(files)!r}).items():
 p=s/name
 if p.is_symlink():p.unlink()
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(source)
(b/'NFB_tmp').mkdir(exist_ok=True)
patch=b/'NFB_KMX.patch';patch.write_text({(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()!r})
subprocess.run(['git','apply','--reverse','--check',str(patch)],cwd=s,check=True)
pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NFB_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n');print(json.dumps(pins))
'''
r=ssh(a,'python3',code);(E/'NFB_NATIVE_SETUP.log').write_text(r.stderr);assert r.returncode==0,r.stderr
(E/'NFB_SOURCE_PINS.json').write_text(r.stdout)
