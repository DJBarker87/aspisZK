from NJN_native import *
s=(E/'NJN_sdk.rs.txt').read_text()
for i,h in [(5,'shared_contract'),(6,'shared_counter_control'),(7,'shared_cell_control'),(8,'exclusive_contract')]:
 r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
 import lzma
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'VERIFICATION' not in log:break
