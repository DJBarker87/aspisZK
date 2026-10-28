from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_install.rs').read_text()
attrs='''#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
# Actual source callee, not the forwarding wrapper.
s+='#[kani::proof_for_contract(aspis_core::field::M31::from_le_bytes)]\n'+attrs+'fn NCG_actual_decoder_contract(){let b:[u8;4]=kani::any();let _=M31::from_le_bytes(b);}\n'
for neg in [False,True]:
 s+='#[kani::proof]\n'+attrs+'#[kani::stub_verified(aspis_core::field::M31::from_le_bytes)]\nfn NCG_actual_base_decoder'+('_negative' if neg else '')+'(){'
 s+='''let q:[u8;608]=kani::any();let slot:usize=kani::any();let term:usize=kani::any();kani::assume(slot<4&&term<26);let offset=slot*120+term*4;
 let scalar=M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap());
 let native=u32::from_le_bytes([q[offset],q[offset+1],q[offset+2],q[offset+3]]);
 let expected=if native<2147483647{Some(M31(native))}else{None};
'''
 s+=('assert_ne!(scalar,expected);' if neg else 'assert_eq!(scalar,expected);')+'kani::cover!(slot==3&&term==25);kani::cover!(native>=2147483647);}\n'
# The exact field-crate annotation is scoped only to Kani in scratch.
annotation='#[cfg_attr(kani, kani::ensures(|r:&Option<M31>|match r{Some(v)=>v.0==u32::from_le_bytes(bytes)&&v.0<P,None=>u32::from_le_bytes(bytes)>=P}))]\n    '
(E/'NCG_decoder_annotation.txt').write_text(annotation)
Path('/tmp/NCG_install_actual.rs').write_text(s)
(E/'NCG_install_actual.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
