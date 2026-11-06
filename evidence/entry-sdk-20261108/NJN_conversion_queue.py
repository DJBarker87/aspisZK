from NJN_native import *
s=(E/'NJN_conversion.rs.txt').read_text()
refs=(E/'NJN_reference.rs').read_text()
for i,h in [(9,'conversion'),(10,'conversion_control'),(11,'pda_conversion'),(12,'pda_conversion_control')]:
 r=fresh(f'NJN_K{i:03d}','NJN_conversion::'+h,[('programs/r1-cost-probe/src/lib.rs','NJN_conversion',s),('programs/r1-cost-probe/src/lib.rs','NJN_reference',refs)])
 log=lzma.decompress((E/f'NJN_K{i:03d}'/'stdout.log.xz').read_bytes()).decode()
 if 'VERIFICATION' not in log:break
