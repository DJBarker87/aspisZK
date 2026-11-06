from NJN_native import *
s=(E/'NJN_sdk.rs.txt').read_text()
for i,h in [(14,'shared_contract'),(15,'shared_counter_control'),(16,'shared_cell_control'),(17,'exclusive_contract'),(18,'exclusive_cell_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'VERIFICATION' not in log:break
