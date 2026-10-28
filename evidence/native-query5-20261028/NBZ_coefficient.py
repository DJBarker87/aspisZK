from pathlib import Path
import json,difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_rescue.rs').read_text();s=s[:s.index('#[kani::proof]')]
s+='''
fn NBZ_coefficient_case(negative:bool){
 let g=NBZ_g();let term:usize=kani::any();let k:usize=kani::any();kani::assume(term<29&&k<8);
 let selected=g[term];let words=selected.to_limbs();
 if negative{assert!(words[k]>=2147483647);}else{assert!(words[k]<2147483647);}
 let restored=E::from_limbs(words).unwrap();assert_eq!(restored.to_limbs()[k],selected.to_limbs()[k]);
 kani::cover!(term==0&&k==0);kani::cover!(term==28&&k==7);
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
for neg in [False,True]:s+=attrs+'fn NBZ_coefficient_read'+('_negative' if neg else '')+'(){NBZ_coefficient_case('+str(neg).lower()+');}\n'
Path('/tmp/NBZ_coefficient.rs').write_text(s)
(E/'NBZ_coefficient.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_coefficient.rs')))
