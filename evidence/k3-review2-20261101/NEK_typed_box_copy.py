"""Matching official-copy controls for the typed Box-admission configuration."""
from NEK_common_fidelity import *
from NEK_common_copy import worker_copy
base=read_json(E/'NEK_COMMON_FIDELITY_TYPED.json.xz');upload(base)
for num,neg in [(219,False),(220,True)]:
 a=f'NEK_K{num:03}'
 if (E/a/'receipt.json').exists():continue
 item=dict(attempt=a,original_receipt='evidence/native-front4b-20261028/NDM_K035/receipt.json',cfg='NEK_shape_weak',clause='fidelity',negative=neg)
 # worker_copy's native command shares the exact target-only feature set.
 # Store the actual typed source bundle as the cfg's primary source identity.
 import NEK_common_copy as copier
 old=copier.cfg
 def typed_cfg(i,b):
  x=old(i,b);x['deps_fingerprint']['fidelity_bundle_sha256']=sha((E/'NEK_COMMON_FIDELITY_TYPED.json.xz').read_bytes());return x
 copier.cfg=typed_cfg
 worker_copy(item,base)
 copier.cfg=old
