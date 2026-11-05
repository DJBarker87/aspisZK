"""Exact KMX copy control for the actual32-byte E record, with independent dst."""
from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent;p=E/'NHF_wide.rs.txt';s=p.read_text()+'''
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u32]>::copy_from_slice,KMX_copy_from_slice)]
fn copy_e(){
 let a:[u32;8]=kani::any();let b:[u32;8]=kani::any();let mut j=0;
 while j<8{kani::assume(a[j]<2147483647&&b[j]<2147483647);j+=1;}
 let src=E::from_limbs(a).unwrap();let mut dst=E::from_limbs(b).unwrap();
 unsafe{core::ptr::copy_nonoverlapping(&src,&mut dst,1)};
 let limb:usize=kani::any();kani::assume(limb<8);
 assert!((dst.to_limbs()[limb]==src.to_limbs()[limb])!=cfg!(NHF_invert));
}
''';p.write_text(s)
pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins['crates/aspis-r1-cost-probe/src/NHF_wide.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
p=E/'NHF_native.patch';patch=p.read_text();a=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_wide.rs\n');p.write_text(patch[:a]+''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHF_wide.rs')))
