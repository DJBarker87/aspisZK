from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_install.rs').read_text()
# New smaller source fragments: one actual Wide scalar call and its two QM callees.
s+='''
fn NCG_scale_case(negative:bool){let x=NCG_e();let scalar:u32=kani::any();kani::assume(scalar<2147483647);let k:usize=kani::any();kani::assume(k<8);let out=x.mul_m31(M31(scalar));unsafe{assert_eq!(NCG_SC,2);assert_eq!(NCG_SX[k/4][k%4],x.to_limbs()[k]);assert_eq!(NCG_SY[k/4],scalar);if negative{assert_ne!(out.to_limbs()[k],NCG_SO[k/4][k%4]);}else{assert_eq!(out.to_limbs()[k],NCG_SO[k/4][k%4]);}}}
fn NCG_coefficient_case(which:usize,negative:bool){let a=NCG_e();let b=NCG_e();let c=NCG_e();let d=NCG_e();let scalar:u32=kani::any();kani::assume(scalar<2147483647);let k:usize=kani::any();kani::assume(k<8);
 let input=match which{0=>a.add(b).add(c).add(d),1=>a.sub(b).sub(c).add(d),2=>a.add(b).sub(c).sub(d),_=>a.sub(b).add(c).sub(d)};
 let out=input.mul_m31(M31(scalar));
 unsafe{assert_eq!(NCG_SC,2);assert_eq!(NCG_SX[k/4][k%4],input.to_limbs()[k]);assert_eq!(NCG_SY[k/4],scalar);if negative{assert_ne!(out.to_limbs()[k],NCG_SO[k/4][k%4]);}else{assert_eq!(out.to_limbs()[k],NCG_SO[k/4][k%4]);}}
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::stub(aspis_core::field::QM31::mul_m31,NCG_scalar_opaque)]
#[kani::unwind(129)]
'''
for name,call in [('scale','NCG_scale_case(NEG)'),*[(f'coefficient{i}',f'NCG_coefficient_case({i},NEG)') for i in range(4)]]:
 for neg in [False,True]:s+=attrs+'fn NCG_'+name+('_negative' if neg else '')+'(){'+call.replace('NEG',str(neg).lower())+';}\n'
Path('/tmp/NCG_coefficients.rs').write_text(s)
(E/'NCG_coefficients.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
