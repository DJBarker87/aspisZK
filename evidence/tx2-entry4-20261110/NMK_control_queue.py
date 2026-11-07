from NMK_native import *
import lzma
jobs=[('NMK_K030','NMK_auth_return',0),('NMK_K031','NMK_auth_reject',0),('NMK_K032','NMK_auth_perturbed',1),('NMK_K033','NMK_auth_argument_mutant',1),('NMK_K034','NMK_auth_omitted_location',1),('NMK_K035','NMK_copy_negative',1),('NMK_K036','NMK_auth_reject_perturbed',1),('NMK_K037','NMK_auth_reject_argument_mutant',1)]
for a,name,expected in jobs:
 r=native(a,'verifier::candidate::NMK_native::'+name)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert r['exit_status']==expected and 'timed out' not in s and ('VERIFICATION:- SUCCESSFUL' in s if expected==0 else 'VERIFICATION:- FAILED' in s),a
