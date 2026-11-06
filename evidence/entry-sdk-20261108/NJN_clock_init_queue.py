from NJN_native import *
s=(E/'NJN_clock_init.rs.txt').read_text()
# Reuse the already declared conversion sidecar slot, not the frozen SDK.
for i,h in [(18,'clock_default_contract'),(69,'clock_default_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_conversion::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_reference',(E/'NJN_reference.rs').read_text()),('programs/r1-cost-probe/src/lib.rs','NJN_conversion',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log or 'VERIFICATION' not in log:break
