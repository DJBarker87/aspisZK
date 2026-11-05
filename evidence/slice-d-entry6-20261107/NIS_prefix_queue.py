from NIS_native import *
s=''.join(l[1:]for l in (E/'NIS_prefix.patch').read_text().splitlines(True) if l.startswith('+')and not l.startswith('+++'))
for i,name in enumerate(['owned1_header','owned1_header_wrong','owned2_header','owned2_header_wrong'],116):
 r=fresh('NIS_K%03d'%i,'r1_pool_adapter::owned::NIS_prefix::'+name,[('programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','NIS_prefix',s)])
 log=lzma.decompress((E/r['attempt']/'stdout.log.xz').read_bytes()).decode()
 if 'timed out' in log.lower() or 'VERIFICATION:-' not in log or r['exit_status'] not in [0,1]:raise RuntimeError('No admitted semantic verdict; stop queue')
 expected=1 if name.endswith('_wrong') else 0
 if r['exit_status']!=expected:raise RuntimeError('Unexpected semantic verdict; stop without reconciliation')
