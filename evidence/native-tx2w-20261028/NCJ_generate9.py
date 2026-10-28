from NCJ_host import *
import difflib
admit('NCJ_INSTALL011')
r=py(f"from pathlib import Path;print((Path({B!r})/'NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs').read_text(),end='')");assert r.returncode==0
before=r.stdout
extra=r'''
// Actual frozen decoder at one arbitrary32-byte window. All surrounding
// bytes are arbitrary and are not traversed by the verifier helper.
fn field_window_gate<const N:usize>(bad:bool){
 let bytes:[u8;N]=kani::any();let j:usize=kani::any();kani::assume(j<N/32);
 for k in 0..8{let o=32*j+4*k;let w=u32::from_le_bytes([bytes[o],bytes[o+1],bytes[o+2],bytes[o+3]]);kani::assume(w<2147483647);}
 let out=field(&bytes,j);let limbs=out.to_limbs();let k:usize=kani::any();kani::assume(k<8);let o=32*j+4*k;
 let expected=u32::from_le_bytes([bytes[o],bytes[o+1],bytes[o+2],bytes[o+3]]);
 assert!(limbs[k]<2147483647);if bad{assert_ne!(limbs[k],expected);}else{assert_eq!(limbs[k],expected);}
}
'''
attrs='''#[kani::proof] #[kani::unwind(2050)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,crate::KMX_stubs::KMX_clone_from_slice)]
'''
for size in [224,2048]:
 for bad in [False,True]:extra+=attrs+f'fn NCJ_field_{size}_{"negative" if bad else "positive"}(){{field_window_gate::<{size}>({str(bad).lower()});}}\n'
after=before+extra
(E/'NCJ_stage9.patch').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/NCJ_weights.rs',tofile='b/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')))
r=py(f'''from pathlib import Path
p=Path({(B+'/NCJ_src/crates/aspis-r1-cost-probe/src/NCJ_weights.rs')!r});assert p.read_text()=={before!r};p.write_text({after!r})
''');assert r.returncode==0,r.stderr
