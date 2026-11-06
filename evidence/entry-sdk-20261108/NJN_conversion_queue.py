from NJN_native import *
s=(E/'NJN_conversion.rs.txt').read_text()
refs=(E/'NJN_reference.rs').read_text()
for i,h in [(10,'conversion'),(11,'conversion_control'),(12,'pda_conversion'),(13,'pda_conversion_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_conversion::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_reference',refs),('programs/r1-cost-probe/src/lib.rs','NJN_conversion',s)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'VERIFICATION' not in log:break
