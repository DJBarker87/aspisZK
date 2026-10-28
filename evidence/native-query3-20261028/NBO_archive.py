from pathlib import Path
import difflib,subprocess,json,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
name='crates/aspis-r1-cost-probe/src/candidate.rs';base=subprocess.check_output(['git','show',rev+':'+name],text=True)
marker='\n#[cfg(kani)] #[path="NBO_native.rs"] mod NBO_native;\n'
module='crates/aspis-r1-cost-probe/src/NBO_native.rs'
source=(E/'NBO_native.rs.txt').read_text()
def patch(text):return ''.join(difflib.unified_diff(base.splitlines(True),(base+marker).splitlines(True),fromfile='a/'+name,tofile='b/'+name))+''.join(difflib.unified_diff([],text.splitlines(True),fromfile='/dev/null',tofile='b/'+module))
(E/'NBO_harness.patch').write_text(patch(source))
for p in E.glob('NBO_[KG]*/sources/NBO_src'):
 f=p/module
 if f.exists():
  a=p.parents[1];out=E/(a.name+'-harness.patch');out.write_text(patch(f.read_text()))
  pins={str(x.relative_to(p)):dict(sha256=hashlib.sha256(x.read_bytes()).hexdigest(),bytes=x.stat().st_size) for x in p.rglob('*') if x.is_file()}
  (E/(a.name+'-source-pins.json')).write_text(json.dumps(pins,indent=2)+'\n')
  import shutil;shutil.rmtree(p)
