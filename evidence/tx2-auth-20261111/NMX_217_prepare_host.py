from pathlib import Path
import json,hashlib,subprocess,difflib
B=Path.cwd();S=B/'NMX_src'; m=json.loads((B/'NMX_STAGING_MANIFEST.json').read_text())
paths=['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs']
original={p:(S/p).read_text() for p in paths}
for p in paths:
 assert hashlib.sha256((S/p).read_bytes()).hexdigest()==m['files'][p]['sha256'],p
assert hashlib.sha256((S/'Cargo.lock').read_bytes()).hexdigest()==m['files']['Cargo.lock']['sha256']
patch=(B/'NMX_KMX_copy_stubs.patch').read_bytes()
assert hashlib.sha256(patch).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
r=subprocess.run(['git','apply','--check',str(B/'NMX_KMX_copy_stubs.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
subprocess.run(['git','apply',str(B/'NMX_KMX_copy_stubs.patch')],cwd=S,check=True)
p=S/paths[0];s=p.read_text();s=s.replace('//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.','//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.\n#![cfg_attr(kani, feature(allocator_api))]\n#[cfg(kani)] extern crate alloc;')
s+='\n#[cfg(kani)] mod NMX_217_reference;\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] mod NMX_KMX;\n';p.write_text(s)
p=S/paths[1];s=p.read_text();mark='fn decode_lane_from_pool_release('
assert s.count(mark)==1
attrs='''#[cfg_attr(kani, kani::requires(bytes.len() != POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES))]
#[cfg_attr(kani, kani::modifies())]
#[cfg_attr(kani, kani::ensures(|r: &Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>| NMX_217_native::result_matches(r,bytes) != NMX_217_native::INVERSE))]
'''
s=s.replace(mark,attrs+mark);s+='\n#[cfg(kani)] #[path="NMX_217_native.rs"] mod NMX_217_native;\n';p.write_text(s)
for name in ['NMX_217_native.rs','NMX_217_reference.rs']:(S/'programs/r1-cost-probe/src'/name).write_bytes((B/name).read_bytes())
diffs=[]
for p in paths:diffs.extend(difflib.unified_diff(original[p].splitlines(True),(S/p).read_text().splitlines(True),fromfile='a/'+p,tofile='b/'+p))
for name in ['NMX_217_native.rs','NMX_217_reference.rs']:
 p='programs/r1-cost-probe/src/'+name;diffs.extend(difflib.unified_diff([], (S/p).read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+p))
(B/'NMX_217_harness.patch').write_text(''.join(diffs))
print('Prepared scratch-only actual-body contract; no non-cfg shipped-body edits')
