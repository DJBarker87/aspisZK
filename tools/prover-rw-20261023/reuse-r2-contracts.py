#!/usr/bin/env python3
"""Reuse two local framing checks only after source/body/harness identity audits."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/v8-r0-zk-20261009/r1p-final/RealR2_evidence'
O=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/continuation/reused-r2-contracts.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
copy=(E/'native/source.rs').read_text()
s=(R/'crates/aspis-core/src/state_only_hiding.rs').read_text();a=s.index('    pub fn encode(self)');b=s.index('\n}\n',a)
t=(R/'crates/aspis-prover/src/state_only_hiding.rs').read_text();c=t.index('fn derive_state_only_mask_seed_from_entropy_ref(');d=t.index('\npub fn build_state_only_mask_material',c)
assert s[a:b] in copy and t[c:d] in copy
assert 'pub const STATE_ONLY_HIDING_CONTEXT_VERSION: u8 = 1;' in s
assert 'pub const STATE_ONLY_HIDING_CONTEXT_BYTES: usize = 1 + 32 + 32 + 8 + 8;' in s
assert 'aspis:state-only:private-mask-seed:v1' in t and 'aspis:state-only:private-mask-seed:v1' in copy
rows=[]
for label,contract in [('RealR2_context_v1','All context inputs; independently indexed byte frame over 81 positions'),('RealR2_seed_v1','All context/binding/entropy bytes, zero/nonzero guard, exact zero/one hash calls, ordered input slices and arbitrary returned digest')]:
    pins=json.loads((E/(label+'-inputs.json')).read_text())
    checked={str(p.relative_to(R)):sha(p.read_bytes()) for f in pins for p in [E/f]}
    assert all(sha((E/f).read_bytes())==h for f,h in pins.items())
    receipt=E/'native-receipts'/label/'receipt.json';r=json.loads(receipt.read_text());assert r['exit_status']==0
    rows.append(dict(receipt=str(receipt.relative_to(R)),receipt_sha256=sha(receipt.read_bytes()),target=r['command'],domain=contract,archive_inputs=checked,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
x=dict(reused=rows,selected_body_sha256={'StateOnlyHidingContext::encode':sha(s[a:b].encode()),'derive_state_only_mask_seed_from_entropy_ref':sha(t[c:d].encode())},constants_checked=True,qualification='Minimal matching context/error types in retained harness, not a full native caller proof; no freshness or random-oracle law established',whole_leaf_gate_complete=False)
O.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(reused=len(rows),selected_bodies_identical=True,whole_leaf_gate_complete=False)))
