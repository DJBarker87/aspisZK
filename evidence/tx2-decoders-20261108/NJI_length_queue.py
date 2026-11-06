from NJI_native import fresh,E
import lzma
for n,name,wrong in [(36,'policy',True),(37,'registry',False),(38,'registry',True),(39,'entry',False),(40,'entry',True),(41,'master',False),(42,'master',True),(43,'checkpoint',False),(44,'checkpoint',True)]:
 a='NJI_K%03d'%n
 r=fresh(a,'statement:pool_v1::format::NJI_length_cut::'+name,[('crates/aspis-statement/src/pool_v1/format.rs','NJI_length_cut',(E/'NJI_length_cut.rs').read_text())],invert=wrong)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert r['exit_status']==(1 if wrong else 0) and ('VERIFICATION:- FAILED' if wrong else 'VERIFICATION:- SUCCESSFUL') in s,(a,'not expected semantic result')
 assert 'unwinding failures' not in s,(a,'incomplete')
