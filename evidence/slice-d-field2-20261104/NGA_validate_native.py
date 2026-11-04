"""Read-only validation of inherited native support; never runs a prover."""
from pathlib import Path
import importlib.util,sys,json,hashlib
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;T=E.parent/'slice-d-field-20261104'
p=T/'NFT_certify.py';s=importlib.util.spec_from_file_location('NGA_readonly_NFT',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
rows=[]
for a,b in [(24,25),(26,27),(28,29),(78,79),(80,81),(82,83),(84,85),(86,87),(88,89),(98,99)]:
 x,y=m.pair(a,b)
 rows.append(dict(positive=x['attempt'],control=y['attempt'],positive_receipt_sha256=m.sha((T/x['attempt']/'receipt.json').read_bytes()),control_receipt_sha256=m.sha((T/y['attempt']/'receipt.json').read_bytes()),status='VALID_SUPPORT_ONLY'))
for a,b in [(30,31),(32,33)]:
 x,y=m.copy_pair(a,b);rows.append(dict(positive=x['attempt'],control=y['attempt'],status='VALID_COPY_SUPPORT_ONLY'))
x,_=m.native(100,1);assert '--cfg NFT_bad_argument' in x['env']['RUSTFLAGS']
rows.append(dict(control='NFT_K100',status='VALID_ARGUMENT_CONTROL_ONLY'))
expected=json.loads((E/'NGA_NATIVE_PINS.json').read_text())
for name,pin in expected.items():assert m.sha((E.parents[1]/name).read_bytes())==pin['sha256']
patch=E.parents[1]/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch'
assert m.sha(patch.read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
result=dict(status='PASS',mode='read-only inherited certificate validation; no Kani rerun',checks=rows,NFT_validator_sha256=m.sha(p.read_bytes()),KMX_patch_sha256=m.sha(patch.read_bytes()),closure_credit=False)
(E/'NGA_NATIVE_REVALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'support_groups':len(rows),'closure_credit':False}))
