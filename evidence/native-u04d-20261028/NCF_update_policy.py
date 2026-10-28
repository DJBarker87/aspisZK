from pathlib import Path
import sys,importlib.util,json,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'native-u04c-20261028';sys.argv=['ncf','unused'];sp=importlib.util.spec_from_file_location('inherited',P/'NCC_native.py');m=importlib.util.module_from_spec(sp)
exec(compile((P/'NCC_native.py').read_text().replace('NCC_NATIVE_TRANSPORT','NCF_NATIVE_TRANSPORT'),str(P/'NCC_native.py'),'exec'),m.__dict__);m.E=E
m.admit('NCF_POLICY_CARRIER_REPAIR')
files={'crates/aspis-statement/src/NCF_policy.rs':(E/'NCF_policy.rs.txt').read_text(),'programs/r1-cost-probe/src/NCF_sdk.rs':(E/'NCF_sdk.rs.txt').read_text()+(E/'NCF_sdk_reject.rs.txt').read_text()}
r=m.py('from pathlib import Path; import json,hashlib; b=Path('+repr(m.B)+')/"NBU_src"; fs='+repr(files)+'; old={n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in fs}; [(b/n).write_text(s) for n,s in fs.items()]; print(json.dumps(dict(before=old,after={n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in fs})))');assert r.returncode==0,r.stdout+r.stderr
(E/'NCF_POLICY_CARRIER_REPAIR.json').write_text(r.stdout)
