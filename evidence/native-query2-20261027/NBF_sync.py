from NBF_host import *
import hashlib,difflib
admit('NBF_SYNC'+str(max([int(p.name.split('-')[0][8:]) for p in E.glob('NBF_SYNC*-reservation.json')]+[0])+1).zfill(3))
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
f='crates/aspis-r1-cost-probe/src/verifier.rs'
original=subprocess.check_output(['git','show',rev+':'+f],text=True)
marker='\n#[cfg(kani)] #[path="NBF_harness.rs"] mod NBF_harness;\n'
harness=(E/'NBF_harness.rs.txt').read_text()
patch=''.join(difflib.unified_diff(original.splitlines(True),(original+marker).splitlines(True),fromfile='a/'+f,tofile='b/'+f))
patch+=''.join(difflib.unified_diff([],harness.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBF_harness.rs'))
(E/'NBF_harness.patch').write_text(patch)
r=py(f'''from pathlib import Path
import hashlib
b=Path({(B+'/NBF_src')!r});p=b/{f!r};s=p.read_text();expected={original!r};marker={marker!r}
assert s==expected or s==expected+marker
p.write_text(expected+marker)
(b/'crates/aspis-r1-cost-probe/src/NBF_harness.rs').write_text({harness!r})
''')
assert r.returncode==0,r.stderr
