from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
get=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
manifest={}
for original,name in [('crates/aspis-core/src/field.rs','KMY_field.rs'),('crates/aspis-core/src/field/wide_exact.rs','KMY_wide_exact.rs')]:
 s=get(original);before=s
 s=s.replace('mod wide_exact;','#[path="KMY_wide_exact.rs"] mod wide_exact;')
 s=re.sub(r'(out\[[^;\n]+?\]|chunk)\.copy_from_slice\(([^;\n]+)\);',r'crate::KMX_stubs::KMX_copy_from_slice(\1,\2);',s)
 # Mutable indexed places need an explicit borrow at the direct call.
 s=re.sub(r'KMX_copy_from_slice\((out\[[^;\n]+?\]),',r'KMX_copy_from_slice(&mut \1,',s)
 (E/name).write_text(s)
 manifest[original]=dict(frozen_sha256=hashlib.sha256(before.encode()).hexdigest(),overlay_sha256=hashlib.sha256(s.encode()).hexdigest(),changes='module path and explicit calls to validated copy loop only')
(E/'KMY_serializer_sources.json').write_text(json.dumps(manifest,indent=2)+'\n')
p=E/'KMY_windows.rs';s=p.read_text();s+='''
#[path="KMY_field.rs"] mod field;
use field::{WideExact as E,QM31 as K,CM31,M31};
fn any_e()->E {let raw:[u32;8]=kani::any();for x in raw{kani::assume(x<0x7fff_ffff);}E::from_limbs(raw).unwrap()}
#[kani::proof] #[kani::unwind(33)]
fn KMY_wide_one_window() {
 let e=any_e();let raw=e.to_limbs();let src=e.to_le_bytes();
 let mut dst:[u8;64]=kani::any();let pos:usize=kani::any();kani::assume(pos<=32);
 let j:usize=kani::any();kani::assume(j<64);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+32],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+32{let b=j-pos;raw[b/4].to_le_bytes()[b%4]}else{old});
}
#[kani::proof] #[kani::unwind(5)]
fn KMY_limb_window() {
 let raw:u32=kani::any();let src=raw.to_le_bytes();let mut dst:[u8;32]=kani::any();
 let pos:usize=kani::any();kani::assume(pos<=28);let j:usize=kani::any();kani::assume(j<32);let old=dst[j];
 KMX_stubs::KMX_copy_from_slice(&mut dst[pos..pos+4],&src);
 assert_eq!(dst[j],if pos<=j && j<pos+4{(raw>>(8*(j-pos)))as u8}else{old});
}
''';p.write_text(s)
