from pathlib import Path
import importlib.util,sys,json
E=Path(__file__).resolve().parent;P=E.parent/'native-u04c-20261028';sys.argv=['ncf','unused'];sp=importlib.util.spec_from_file_location('inherited',P/'NCC_native.py');m=importlib.util.module_from_spec(sp)
exec(compile((P/'NCC_native.py').read_text().replace('NCC_NATIVE_TRANSPORT','NCF_NATIVE_TRANSPORT'),str(P/'NCC_native.py'),'exec'),m.__dict__);m.E=E
m.admit('NCF_PROGRAM_REPAIR')
r=m.py('from pathlib import Path; import json,hashlib; p=Path('+repr(m.B)+')/"NBU_src/programs/r1-cost-probe/src/lib.rs"; s=p.read_text(); old=hashlib.sha256(s.encode()).hexdigest(); first,rest=s.split("\\n",1); assert "feature(allocator_api)" not in s; s=first+"\\n#![cfg_attr(kani, feature(allocator_api))]\\n#[cfg(kani)]\\nextern crate alloc;\\n"+rest; p.write_text(s); print(json.dumps(dict(before=old,after=hashlib.sha256(p.read_bytes()).hexdigest(),change="cfg-only allocator API feature and extern alloc for exact KMX module")))');assert r.returncode==0,r.stdout+r.stderr
(E/'NCF_PROGRAM_REPAIR.json').write_text(r.stdout)
