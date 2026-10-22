#!/usr/bin/env python3
"""Verify exact code identity supporting reuse of the pass-2 codec gates."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence';E=B/'ckpt-abi3-20261021'
old=R/'tools/oracle-port-ckpt-abi2/src/lib.rs';new=R/'tools/oracle-port-ckpt-abi3/src/lib.rs'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
prefix=lambda s:s.split('#[cfg(kani)] mod proofs {')[0].replace('extern crate alloc;\n','')
assert prefix(old.read_text())==prefix(new.read_text())
helper=lambda s:s.split('#[cfg(kani)] mod proofs {')[1].split('#[derive(Clone,Copy)]')[0]
assert helper(old.read_text())==helper(new.read_text())
rows=[]
for name in ['final-decode-k','final-decode-e','final-encode-k','final-encode-e-byte']:
 p=B/'ckpt-abi2-20261021/host/receipts'/name
 d=json.loads((p/'receipt.json').read_text())
 assert d['exit_status']==0 and d['swaps']==0
 assert d['source_sha256']['tools/oracle-port-ckpt-abi2/src/lib.rs']==sha(old)
 assert 'VERIFICATION SUCCESSFUL' in (p/'stdout.log').read_text()
 assert '--unwinding-assertions' in d['target']
 rows.append(dict(receipt=str((p/'receipt.json').relative_to(R)),receipt_sha256=sha(p/'receipt.json'),source_sha256=sha(old),target=d['target']))
result=dict(schema='checkpoint-codec-exact-code-reuse-v1',normalization='only unused extern crate alloc declaration removed before comparison',specs_helpers_contracts_and_contract_roots_identical=True,common_prefix_sha256=hashlib.sha256(prefix(old.read_text()).encode()).hexdigest(),receipts=rows,trust='existing P6 Kani contracts, not kernel theorems or a full-reader certificate')
(E/'reused-codec-contracts.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='receipts'}))
