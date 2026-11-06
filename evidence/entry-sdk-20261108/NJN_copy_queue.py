from NJN_native import *
s=(E/'NJN_copy.rs.txt').read_text()
for i,h in [(65,'exclusive_window'),(66,'exclusive_window_corrupt'),(67,'exclusive_window_frame')]:
 r=fresh(f'NJN_K{i:03d}','NJN_sdk::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_sdk',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log or (i==65) and r['exit_status']!=0:break
