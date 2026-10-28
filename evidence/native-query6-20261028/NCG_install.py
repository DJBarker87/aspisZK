from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s=Path('/tmp/NCG_shapes.rs').read_text()
attrs='''#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
s+='''
#[kani::requires(index<4)]
#[kani::ensures(|r:&u64|*r==row[index])]
fn NCG_row_get(row:&[u64;4],index:usize)->u64{residue_limb_at(row,index)}
#[kani::requires(index<4)]
#[kani::ensures(|r:&u64|*r!=row[index])]
fn NCG_row_get_wrong(row:&[u64;4],index:usize)->u64{residue_limb_at(row,index)}
#[kani::requires(index<4)]
#[kani::ensures(|r:&u32|*r==limbs[index])]
fn NCG_power_get(limbs:&[u32;4],index:usize)->u32{power_limb_at(limbs,index)}
#[kani::requires(index<4)]
#[kani::ensures(|r:&u32|*r!=limbs[index])]
fn NCG_power_get_wrong(limbs:&[u32;4],index:usize)->u32{power_limb_at(limbs,index)}
#[kani::ensures(|r:&Option<M31>|match r{Some(v)=>v.0==u32::from_le_bytes(bytes)&&v.0<2147483647,None=>u32::from_le_bytes(bytes)>=2147483647})]
fn NCG_decoder(bytes:[u8;4])->Option<M31>{M31::from_le_bytes(bytes)}
#[kani::ensures(|r:&Option<M31>|!match r{Some(v)=>v.0==u32::from_le_bytes(bytes)&&v.0<2147483647,None=>u32::from_le_bytes(bytes)>=2147483647})]
fn NCG_decoder_wrong(bytes:[u8;4])->Option<M31>{M31::from_le_bytes(bytes)}
'''
for typ,setup,args in [('row_get','let row:[u64;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);','&row,i'),('power_get','let row:[u32;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);','&row,i'),('decoder','let bytes:[u8;4]=kani::any();','bytes')]:
 for neg in [False,True]:
  fn='NCG_'+typ+('_wrong' if neg else '')
  s+=f'#[kani::proof_for_contract({fn})]\n'+attrs+f'fn NCG_{typ}_callee'+('_negative' if neg else '')+f'(){{{setup}let _={fn}({args});}}\n'
# Exact source getter calls installed through checked wrapper; wrappers are not renamed source callees.
for typ,setup,args,expected in [('row_get','let row:[u64;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);','&row,i','row[i]'),('power_get','let row:[u32;4]=kani::any();let i:usize=kani::any();kani::assume(i<4);','&row,i','row[i]'),('decoder','let bytes:[u8;4]=kani::any();','bytes','if u32::from_le_bytes(bytes)<2147483647{Some(M31(u32::from_le_bytes(bytes)))}else{None}')]:
 for neg in [False,True]:
  op='assert_ne!' if neg else 'assert_eq!'
  s+=f'#[kani::proof]\n#[kani::stub_verified(NCG_{typ})]\n'+attrs+f'fn NCG_{typ}_caller'+('_negative' if neg else '')+f'(){{{setup}{op}(NCG_{typ}({args}),{expected});}}\n'
Path('/tmp/NCG_install.rs').write_text(s)
(E/'NCG_install.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
