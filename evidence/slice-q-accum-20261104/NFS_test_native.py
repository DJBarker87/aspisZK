from pathlib import Path
import json,copy
from NFS_native_association import check
E=Path(__file__).resolve().parent
f=json.loads((E.parent/'slice-q-mul7-20261104/NFF_FROZEN.json').read_text());tests=[]
x=copy.deepcopy(f);p='crates/aspis-r1-cost-probe/src/verifier.rs';x[p]=x[p].replace('line_z:Vec<M31>','line_z:Vec<CM31>');tests.append(('non-M31 geometry receiver',dict(frozen=x)))
x=copy.deepcopy(f);p='crates/aspis-r1-cost-probe/src/candidate.rs';x[p]=x[p].replace('let node = z.mul(z).double().sub(M31::ONE);','let node = z.mul(z).double();');tests.append(('changed node chain',dict(frozen=x)))
n=json.loads((E.parent/'slice-q-values-20261104/NFP_NATIVE_VALIDATION.json').read_text());x=copy.deepcopy(n);x['rename_families']=0;tests.append(('missing rename family',dict(native=x)))
x=copy.deepcopy(n);x['exact_KMX_patch_sha256']='0'*64;tests.append(('wrong copy patch',dict(native=x)))
rejected=[]
for name,args in tests:
 try:check(**args)
 except ValueError:rejected.append(name)
 else:raise AssertionError('mutation admitted '+name)
(E/'NFS_NATIVE_MUTATIONS.json').write_text(json.dumps(dict(status='PASS',rejected=rejected),indent=1)+'\n');print(rejected)
