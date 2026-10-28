from NBF_host import *
from NBF_payloads import read_payload
import hashlib,difflib
admit('NBF_SYNC'+str(max([int(p.name.split('-')[0][8:]) for p in E.glob('NBF_SYNC*-reservation.json')]+[0])+1).zfill(3))
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
f='crates/aspis-r1-cost-probe/src/verifier.rs'
original=subprocess.check_output(['git','show',rev+':'+f],text=True)
marker='\n#[cfg(kani)] #[path="NBF_harness.rs"] mod NBF_harness;\n'
harness=read_payload('NBF_harness.rs')
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

# Additional cfg(kani)-only child module at the actual private candidate cut.
f2='crates/aspis-r1-cost-probe/src/candidate.rs'
o2=subprocess.check_output(['git','show',rev+':'+f2],text=True)
m2='\n#[cfg(kani)] #[path="NBF_query.rs"] mod NBF_query;\n'
try:h2=read_payload('NBF_query.rs')
except FileNotFoundError:h2=''
if h2:
 patch+=''.join(difflib.unified_diff(o2.splitlines(True),(o2+m2).splitlines(True),fromfile='a/'+f2,tofile='b/'+f2))
 patch+=''.join(difflib.unified_diff([],h2.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBF_query.rs'))
 (E/'NBF_harness.patch').write_text(patch)
 r=py(f"""from pathlib import Path
b=Path({(B+'/NBF_src')!r})
p=b/{f2!r};s=p.read_text();assert s=={o2!r} or s=={(o2+m2)!r}
p.write_text({(o2+m2)!r});(b/'crates/aspis-r1-cost-probe/src/NBF_query.rs').write_text({h2!r})
 """)
 assert r.returncode==0,r.stderr
