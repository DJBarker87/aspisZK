import NBY_generate as g
# Exact validated KMX copy implementation, restricted to one source/dest byte.
# This is a mitigation-window gate, not an unproved replacement copy stub.
common='''let mut idx:[u32;16]=kani::any();let mut val:[[u8;32];16]=kani::any();let reply:[u8;32]=kani::any();let i:usize=kani::any();let w:usize=kani::any();let c:usize=kani::any();let k:usize=kani::any();let z:usize=kani::any();kani::assume(i<16&&w<=i&&c<32&&k<16&&z<32);let old_i=idx[k];let old_v=val[k][z];let parent=index_at(&idx,i)>>Arity::Two.bits();'''
for part in ['index_and_byte','byte_inside','byte_outside','pointer_geometry']:
 body=common
 if part=='byte_inside':body+='kani::assume(k==w&&z==c);'
 if part=='byte_outside':body+='kani::assume(k!=w||z!=c);'
 if part=='pointer_geometry':
  body+='let p=val[w].as_mut_ptr().wrapping_add(c);let q=&mut val[w][c] as *mut u8;'
  expr='p==q&&idx[k]==old_i&&val[k][z]==old_v'
 else:
  body+='''idx[w]=parent;unsafe{crate::KMX_stubs::KMX_copy_nonoverlapping(reply.as_ptr().wrapping_add(c),val[w].as_mut_ptr().wrapping_add(c),1)};'''
  expr='idx[k]==if k==w{parent}else{old_i}&&val[k][z]==if k==w&&z==c{reply[c]}else{old_v}'
 g.pair('write_'+part,body,expr)
if __name__=='__main__':g.publish('NBY_write_windows','multiproof.rs',81)
