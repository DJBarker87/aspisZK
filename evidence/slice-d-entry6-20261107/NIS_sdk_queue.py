from NIS_native import *
s=''.join(l[1:]for l in (E/'NIS_sdk.patch').read_text().splitlines(True) if l.startswith('+')and not l.startswith('+++'))
for i,name in enumerate(['first0', 'first0_wrong', 'first1', 'first1_wrong', 'first2', 'first2_wrong', 'second0', 'second0_wrong', 'second1', 'second1_wrong', 'second2', 'second2_wrong', 'second3', 'second3_wrong', 'second4', 'second4_wrong', 'second5', 'second5_wrong', 'second6', 'second6_wrong', 'first0_stability', 'second0_stability'],74):
 r=fresh('NIS_K%03d'%i,'r1_pool_adapter::owned::NIS_sdk::'+name,[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NIS_sdk',s)])
 log=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log.lower() or r['exit_status'] not in [0,1]:break
