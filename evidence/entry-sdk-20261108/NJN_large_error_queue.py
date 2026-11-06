from NJN_native import *
s=(E/'NJN_large_error.rs.txt').read_text()
for i,h in [(17,'shared_contract'),(18,'shared_counter_control'),(69,'shared_cell_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log or i==17 and r['exit_status']!=0:break
