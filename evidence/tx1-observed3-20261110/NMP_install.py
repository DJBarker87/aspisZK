from pathlib import Path
import json,shutil,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NMP_src'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
patch='';expected={}
for n,r in json.loads((B/'NMP_POOL_FROZEN.json').read_text()).items():
 p=S/n;p.parent.mkdir(parents=True,exist_ok=True);raw=__import__('base64').b64decode(r['base64']);assert hashlib.sha256(raw).hexdigest()==r['sha256'];p.write_bytes(raw)
n='crates/aspis-r1-cost-probe/src/lib.rs';p=S/n;before=p.read_text();prefix='#![cfg_attr(kani,feature(allocator_api))]\n'
if before.startswith(prefix):before=before[len(prefix):]
expected[n]=hashlib.sha256(before.encode()).hexdigest();p.write_text(prefix+before)
patch+=''.join(difflib.unified_diff(before.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
for n,module in [('crates/aspis-r1-cost-probe/src/r1_semantic.rs','NMP_native'),('crates/aspis-r1-cost-probe/src/r1_wire.rs','NMP_factory'),('crates/aspis-r1-cost-probe/src/candidate.rs','NMP_prepare'),('crates/aspis-core/src/field/wide_exact.rs','NMP_field')]:
 p=S/n
 suffix='\n#[cfg(kani)]\n#[path = "'+module+'.rs"]\npub(crate) mod '+module+';\n'
 before=p.read_text()
 if before.endswith(suffix):before=before[:-len(suffix)]
 expected[n]=hashlib.sha256(before.encode()).hexdigest();p.write_text(before+suffix)
 patch+=''.join(difflib.unified_diff(before.splitlines(True),p.read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n))
 for mod in ([module,'NMP_helpers'] if module=='NMP_native' else [module]):
  q=p.with_name(mod+'.rs');q.write_text((B/(mod+'.rs.txt')).read_text())
  patch+=''.join(difflib.unified_diff([],q.read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+str(q.relative_to(S))))
(B/'NMP_HARNESSES.patch').write_text(patch);(B/'NMP_HARNESSES.patch.sha256').write_text(sha(B/'NMP_HARNESSES.patch')+'\n')
allpins={str(p.relative_to(S)):sha(p) for root in [S/'crates',S/'programs'] for p in root.rglob('*') if p.is_file()}
release=json.loads((B/'NMP_FROZEN_PINS.json').read_text())
release.update({n:r['sha256'] for n,r in json.loads((B/'NMP_POOL_FROZEN.json').read_text()).items()})
for n,h in expected.items():assert release[n]==h,('frozen overlay base mismatch',n)
(B/'NMP_SOURCE_PINS.json').write_text(json.dumps(allpins,indent=1));(B/'NMP_FROZEN_FILE_PINS.json').write_text('{}');(B/'NMP_BASE_EXPECTED.json').write_text(json.dumps(release,indent=1))
print('Installed NMP cfg-only harnesses; hashes and patch recorded')
