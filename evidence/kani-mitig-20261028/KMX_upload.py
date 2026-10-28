"""Upload our inputs after admission; retry only transient transport failures."""
from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KMX_host as h
h.admit(sys.argv[1])
payload={h.B+'/KMX_gate.py':(E/'KMX_gate.py').read_text()}
for p in E.glob('KMX_*.rs.txt'):payload[h.B+'/KMX_src/crates/aspis-r1-cost-probe/src/'+p.name[:-4]]=p.read_text()
payload[h.B+'/KMX_CopyMeaning.lean']=(E.parents[1]/'lean/KMX_CopyMeaning.lean').read_text()
for name,text in payload.items():
 r=h.remote_py('from pathlib import Path\np=Path('+repr(name)+')\np.write_text('+repr(text)+')')
 assert r.returncode==0,r.stderr
print('uploaded own sources',len(payload))

r=h.remote_py('from pathlib import Path\np=Path('+repr(h.B+'/KMX_src/crates/aspis-r1-cost-probe/src/lib.rs')+')\ns=p.read_text()\nif not s.startswith("#![feature(allocator_api)]"):p.write_text("#![feature(allocator_api)]\\n"+s)\nprint("scratch allocator_api enabled")')
assert r.returncode==0,r.stderr
print(r.stdout)
