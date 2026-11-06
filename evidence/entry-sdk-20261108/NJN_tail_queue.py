from NJN_native import *
# Alternate, genuinely smaller native interface for the timed-out String carrier:
# no proof-for-contract return havoc; execute the actual SDK converter and keep
# a single arbitrary coordinate. This remains support, not the NCO contract gate.
s=(E/'NJN_conversion_split.rs.txt').read_text()
a=s.index('#[kani::proof_for_contract(borsh_coordinate)]');s=s[:a]+'''
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borsh_window(){let i:usize=kani::any();kani::assume(i<7);let r=ProgramError::from(15u64<<32);match r{ProgramError::BorshIoError(s)=>{assert_eq!(s.len(),7);assert_eq!(s.as_bytes()[i],b"Unknown"[i]);},_=>assert!(false)}}
#[kani::proof] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn borsh_window_control(){let i:usize=kani::any();kani::assume(i<7);let r=ProgramError::from(15u64<<32);match r{ProgramError::BorshIoError(s)=>{assert_eq!(s.len(),7);assert_eq!(s.as_bytes()[i],b"Unknown"[i]^1);},_=>assert!(false)}}
'''
(E/'NJN_borsh_direct.rs.txt').write_text(s)
for i,h in [(68,'borsh_window'),(70,'borsh_window_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_conversion::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_reference',(E/'NJN_reference.rs').read_text()),('programs/r1-cost-probe/src/lib.rs','NJN_conversion',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log or (i==68) and r['exit_status']!=0:break
