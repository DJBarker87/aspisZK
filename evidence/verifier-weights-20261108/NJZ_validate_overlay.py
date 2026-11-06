from pathlib import Path
import json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;d=json.load(open(E/'NJZ_NATIVE_INPUTS.json'));rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';rows=[];patch=[]
allowed={
'crates/aspis-r1-cost-probe/src/lib.rs':['#![cfg_attr(kani, feature(allocator_api))]\n','\n#[cfg(kani)] include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));\n'],
'crates/aspis-r1-cost-probe/src/verifier.rs':['\n#[cfg(kani)]\n#[path="NJZ_native.rs"]\nmod NJZ_native;\n'],
'crates/aspis-core/src/field.rs':['#[cfg_attr(kani, derive(kani::Arbitrary))]\n'],
'crates/aspis-statement/src/pool_v1/incremental_merkle.rs':['#[cfg_attr(kani, derive(kani::Arbitrary))]\n']}
for n,text in d.items():
 if not n.startswith(('crates/','programs/')):continue
 if n.endswith('/NJZ_native.rs'):
  frozen='';kind='own cfg(kani)-only harness module'
 else:
  frozen=subprocess.check_output(['git','show',rev+':'+n],text=True);stripped=text
  for addition in allowed.get(n,[]):
   assert stripped.count(addition)==1,(n,addition)
   stripped=stripped.replace(addition,'',1)
  assert stripped==frozen,('STOP executable frozen-source drift',n)
  kind='frozen body identical after exact cfg(kani)-only additions'
 rows.append(dict(file=n,kind=kind,payload_sha256=hashlib.sha256(text.encode()).hexdigest(),frozen_sha256=hashlib.sha256(frozen.encode()).hexdigest()))
 patch.extend(difflib.unified_diff(frozen.splitlines(True),text.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJZ_native.patch').write_text(''.join(patch));(E/'NJZ_OVERLAY_IDENTITY.json').write_text(json.dumps(dict(status='PASS',frozen_revision=rev,rows=rows),indent=2)+'\n')
print('Frozen overlay identity PASS: only exact cfg(kani) additions and prefix-owned scratch harness.')
