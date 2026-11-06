from NJN_native import *
s=(E/'NJN_sdk.rs.txt').read_text()
for i,h in [(1,'shared_contract'),(2,'shared_counter_control'),(3,'shared_cell_control'),(4,'exclusive_contract')]:
 r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
 if r['exit_status'] not in [0,1]:break
