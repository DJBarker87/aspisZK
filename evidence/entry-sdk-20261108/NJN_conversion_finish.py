from NJN_native import *
s=(E/'NJN_conversion_split.rs.txt').read_text().replace('let _=ProgramError::from(status);ProgramError::Custom(17)','ProgramError::Custom((status as u32)^1)')
(E/'NJN_conversion_finish.rs.txt').write_text(s)
for i,h in [(21,'builtin_control'),(22,'custom'),(23,'custom_control'),(24,'borsh_window'),(68,'borsh_window_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_conversion::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_reference',(E/'NJN_reference.rs').read_text()),('programs/r1-cost-probe/src/lib.rs','NJN_conversion',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log:break
