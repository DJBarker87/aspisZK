from NMK_native import *
for a,target,expected in [('NMK_K040','KMX_ptr_correct',0),('NMK_K041','KMX_ptr_wrong',1)]:
 r=native(a,'verifier::candidate::NMK_native::KMX_checks::'+target)
 raw=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert r['exit_status']==expected and 'timed out' not in raw and ('VERIFICATION:- SUCCESSFUL' in raw if expected==0 else 'VERIFICATION:- FAILED' in raw),a
 if expected:assert 'Failed Checks:' in raw and 'unwinding assertion' not in raw.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0],a
