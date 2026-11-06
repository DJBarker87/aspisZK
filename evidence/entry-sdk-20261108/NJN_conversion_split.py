from NJN_native import *
s=(E/'NJN_conversion.rs.txt').read_text()
s+='''
#[kani::proof_for_contract(convert)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn builtin(){let tag:u64=kani::any();kani::assume(tag>=2 && tag<=26 && tag!=15);let _=convert(tag<<32);}
#[kani::proof_for_contract(convert_bad)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn builtin_control(){let tag:u64=kani::any();kani::assume(tag>=2 && tag<=26 && tag!=15);let _=convert_bad(tag<<32);}
#[kani::proof_for_contract(convert)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn custom(){let s:u64=kani::any();kani::assume(s&0xffff_ffff!=0 || (s>>32)>26 || s==0 || s==(1u64<<32));let _=convert(s);}
#[kani::proof_for_contract(convert_bad)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn custom_control(){let s:u64=kani::any();kani::assume(s&0xffff_ffff!=0 || (s>>32)>26 || s==0 || s==(1u64<<32));let _=convert_bad(s);}
#[kani::requires(i<7)]
#[kani::ensures(|r|matches!(r,ProgramError::BorshIoError(s)if s.len()==7 && s.as_bytes()[i]==b"Unknown"[i]))]
fn borsh_coordinate(i:usize)->ProgramError{ProgramError::from(15u64<<32)}
#[kani::requires(i<7)]
#[kani::ensures(|r|matches!(r,ProgramError::BorshIoError(s)if s.len()==7 && s.as_bytes()[i]==b"Unknown"[i]))]
fn borsh_coordinate_bad(i:usize)->ProgramError{let mut s=String::from("Unknown");unsafe{s.as_bytes_mut()[i]^=1;}ProgramError::BorshIoError(s)}
#[kani::proof_for_contract(borsh_coordinate)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borsh_window(){let i:usize=kani::any();kani::assume(i<7);let _=borsh_coordinate(i);}
#[kani::proof_for_contract(borsh_coordinate_bad)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borsh_window_control(){let i:usize=kani::any();kani::assume(i<7);let _=borsh_coordinate_bad(i);}
'''
(E/'NJN_conversion_split.rs.txt').write_text(s)
for i,h in [(19,'builtin'),(20,'builtin_control'),(21,'custom'),(22,'custom_control'),(23,'borsh_window'),(24,'borsh_window_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_conversion::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_reference',(E/'NJN_reference.rs').read_text()),('programs/r1-cost-probe/src/lib.rs','NJN_conversion',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log:break
