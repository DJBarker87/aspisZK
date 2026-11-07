from NMN_native import *
import lzma
base='verifier::candidate::NMN_native::'
items=[(14,'NMN_auth_return',True),(15,'NMN_auth_reject',True),(16,'NMN_auth_reply_control',False),(17,'NMN_auth_argument_control',False),(18,'NMN_auth_write_control',False),(19,'NMN_reject_reply_control',False),(20,'NMN_reject_argument_control',False),(21,'NMN_reject_write_control',False),(22,'NMN_common_stop_control',False),(23,'NMN_auth_return_stability',True),(24,'NMN_auth_reply_stability',False),(25,'KMX_checks::KMX_ptr_correct',True),(26,'KMX_checks::KMX_ptr_wrong',False)]
for i,name,positive in items:
 a=f'NMN_K{i:03d}';r=native(a,base+name)
 s=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 if positive:assert r['exit_status']==0,(a,s[-2000:])
 else:
  assert r['exit_status']!=0 and 'Failed Checks:' in s and 'CBMC timed out' not in s,(a,s[-2000:])
  failed=s.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0]
  assert 'unwinding assertion' not in failed,(a,failed)
