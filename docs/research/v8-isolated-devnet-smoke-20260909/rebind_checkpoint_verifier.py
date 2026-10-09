#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
h=Path(__file__).resolve().parent;r=h.parents[2]
assert str(r)=='/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909' and not (r/'.git').exists()
alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def key(s):
 n=0
 for c in s:n=n*58+alphabet.index(c)
 return '['+','.join(map(str,n.to_bytes(32,'big')))+']'
old=json.loads((h/'pre-checkpoint-fix-identities.json').read_text())['programs_and_accounts'];new=json.loads((h/'identities.json').read_text())['programs_and_accounts']
p=r/'programs/aspis-verifier/src/v7_pair_forest_dispatch.rs';s=p.read_text();before=hashlib.sha256(s.encode()).hexdigest()
a='const PAIR_FOREST_INVARIANT_POOL_PROGRAM_AUDIT_V1: [u8; 32] = '+key(old['pool'])+';';assert s.count(a)==1
s=s.replace(a,a.replace(key(old['pool']),key(new['pool'])));p.write_text(s)
(h/'checkpoint-verifier-rebind.json').write_text(json.dumps({'old_pool':old['pool'],'new_pool':new['pool'],'old_verifier':old['verifier'],'new_verifier':new['verifier'],'dispatch_before_sha256':before,'dispatch_after_sha256':hashlib.sha256(s.encode()).hexdigest(),'other_verifier_inputs':'unchanged selected COMPLETE kernels and authenticated proof lifecycle; original Poseidon restored'},indent=2)+'\n')
