from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_dots.rs').read_text();s=s[:s.index('#[kani::proof]')]
s+='''
// One actual scalar statement from the eight unrolled source sites. Every
// unobserved coefficient, proof byte and sum coordinate remains symbolic.
fn NBZ_single_case(fixed:usize,negative:bool){
 let q:[u8;608]=kani::any();let g=NBZ_g();let slot:usize=kani::any();let term:usize=kani::any();let phase:usize=kani::any();
 let k:usize=if fixed<8{fixed}else{kani::any()};let j:usize=kani::any();kani::assume(slot<4&&term<26&&phase<4&&k<8&&j<8);
 let offset=slot*120+term*4;let scalar=u32::from_le_bytes([q[offset],q[offset+1],q[offset+2],q[offset+3]]);kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();let before=sums[j];let old=sums[k];kani::assume(old<(1u64<<34)+(phase as u64)*NBZ_D);let coefficient=g[term].to_limbs()[k];
 unsafe{NBZ_PHASE=phase;}
 sums[k]=NBZ_add_expression(sums[k],g[term].to_limbs()[k],scalar);
 unsafe{assert_eq!(NBZ_CALLS,1);assert_eq!(NBZ_OLD[0],old);assert_eq!(NBZ_COEFF[0],coefficient);assert_eq!(NBZ_SCALAR[0],scalar);
 let expected=if j==k{NBZ_OUT[0]}else{before};
 if negative{assert_ne!(sums[j],expected);}else{assert_eq!(sums[j],expected);}}
 kani::cover!(slot==3&&term==25);kani::cover!(phase==0);kani::cover!(phase==3);kani::cover!(j!=k);
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::stub(NBZ_add_expression,NBZ_add_spec)]
#[kani::unwind(129)]
'''
rows=[]
for fixed in [8,*range(8)]:
 for neg in [False,True]:
  name='NBZ_single_'+str(fixed)+('_negative' if neg else '')
  s+=attrs+'fn '+name+'(){NBZ_single_case('+str(fixed)+','+str(neg).lower()+');}\n'
  rows.append(dict(harness='verifier::candidate::NBZ_rescue::'+name,fixed=fixed,negative=neg))
Path('/tmp/NBZ_rescue.rs').write_text(s)
(E/'NBZ_rescue.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_rescue.rs')))
(E/'NBZ_RESCUE_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
