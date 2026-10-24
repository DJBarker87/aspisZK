#!/usr/bin/env python3
"""Source pins for the P6 local opening/leaf lowering; no extraction claim."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2]
def body(s,name):
 a=s.index('fn '+name+'(') if 'fn '+name+'(' in s else s.index('fn '+name+'<')
 a=s.index('{',a);depth=1;b=a+1
 while depth:
  depth += (s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
paths={'opening':'crates/aspis-r1-cost-probe/src/candidate.rs',
       'batch_leaf':'crates/aspis-r1-cost-probe/src/candidate.rs',
       'private_leaf_hash_with_digest':'crates/aspis-core/src/state_only_private_merkle.rs'}
rows={}
for n,p in paths.items():
 current=body((R/p).read_text(),n)
 old=body(subprocess.check_output(['git','show','b2727acd3:'+p],cwd=R,text=True),n)
 assert current==old,n
 rows[n]={'path':p,'body_sha256':hashlib.sha256(current.encode()).hexdigest(),'bytes':len(current.encode()),'identical_to':'b2727acd3'}
checks={'opening_expression':'compact::OFF_OPENINGS + i * OPENING' in body((R/paths['opening']).read_text(),'opening'),
 'leaf0':'&q[..480], &salt' in body((R/paths['batch_leaf']).read_text(),'batch_leaf'),
 'leaf1':'&q[480..608], &salt' in body((R/paths['batch_leaf']).read_text(),'batch_leaf'),
 'leaf2':'&q[672..800], &salt' in body((R/paths['batch_leaf']).read_text(),'batch_leaf'),
 'one_digest':'hash.digest(&[&[DOM_LEAF, tree_tag], value, salt])' in body((R/paths['private_leaf_hash_with_digest']).read_text(),'private_leaf_hash_with_digest')}
assert all(checks.values())
out={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'functions':rows,'checks':checks,
 'scope':'Static source-body pins only. Port4B_Opening models release wrapping arithmetic. Port4B_LeafCode is a P6 local lowering with salt array-copy erasure, not a new Charon extraction. The existing P6 leaf cut covers exact address/digest/call count; native parent composition remains separate.'}
(R/'evidence/port4b-20261023/leaf-source-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(checks))
