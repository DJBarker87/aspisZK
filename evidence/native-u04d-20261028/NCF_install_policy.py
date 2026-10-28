"""Own scratch-only contracts and registrations. No production source edit."""
from pathlib import Path
import importlib.util,sys,json,hashlib,difflib
E=Path(__file__).resolve().parent;sys.argv=['ncf','unused'];spec=importlib.util.spec_from_file_location('own',E/'NCF_control.py')
# Reuse only the inherited read-only transport/admission helpers.
P=E.parent/'native-u04c-20261028';spec=importlib.util.spec_from_file_location('transport',P/'NCC_native.py');m=importlib.util.module_from_spec(spec)
exec(compile((P/'NCC_native.py').read_text().replace('NCC_NATIVE_TRANSPORT','NCF_NATIVE_TRANSPORT'),str(P/'NCC_native.py'),'exec'),m.__dict__);m.E=E
m.admit('NCF_POLICY_INSTALL')
files={n:(E/n).read_text() for n in ['NCF_policy.rs.txt','NCF_sdk.rs.txt']}
code=f'''from pathlib import Path
import hashlib,json,difflib
b=Path({m.B!r});s=b/'NBU_src';files={files!r};out=[];patch=''
def change(name,new):
 global patch
 p=s/name;old=p.read_text() if p.exists() else '';p.write_text(new)
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name if old else '/dev/null',tofile='b/'+name))
 out.append(dict(path=name,before=hashlib.sha256(old.encode()).hexdigest(),after=hashlib.sha256(new.encode()).hexdigest()))
f='crates/aspis-statement/src/pool_v1/format.rs';old=(s/f).read_text();assert 'crate::NCF_policy' not in old
assert hashlib.sha256(old.encode()).hexdigest()=='209bf45ab1fbf03fa6a5b524e6b2079068537368b02837e320d708ca5128f88d'
attrs='#[cfg_attr(kani, kani::requires(core::ptr::eq(policy, unsafe {{ crate::NCF_policy::NCF_EXPECTED }})))]\\n#[cfg_attr(kani, kani::ensures(|result: &Result<(),PoolV1FormatError>| *result == crate::NCF_policy::NCF_spec(policy)))]\\n'
change(f,old.replace('pub fn validate_verifier_policy_v1(',attrs+'pub fn validate_verifier_policy_v1(',1))
f='crates/aspis-statement/src/lib.rs';change(f,(s/f).read_text()+'\\n#[cfg(kani)]\\npub mod NCF_policy;\\n')
change('crates/aspis-statement/src/NCF_policy.rs',files['NCF_policy.rs.txt'])
f='programs/r1-cost-probe/src/lib.rs';old=(s/f).read_text();assert 'mod NCF_KMX' not in old;change(f,old+'\\n#[cfg(kani)]\\n#[path = "../../../KMX_stubs.rs"]\\nmod NCF_KMX;\\n')
f='programs/r1-cost-probe/src/r1_pool_adapter.rs';change(f,(s/f).read_text()+'\\n#[cfg(kani)]\\n#[path = "NCF_sdk.rs"]\\nmod NCF_sdk;\\n')
change('programs/r1-cost-probe/src/NCF_sdk.rs',files['NCF_sdk.rs.txt'])
assert hashlib.sha256((s/'KMX_stubs.rs').read_bytes()).hexdigest()=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
print(json.dumps(dict(changes=out,patch=patch,non_cfg_function_body_changed=False)))
'''
r=m.py(code);assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout);(E/'NCF_policy_harness.patch').write_text(x.pop('patch'));(E/'NCF_POLICY_INSTALL.json').write_text(json.dumps(x,indent=2)+'\n')
