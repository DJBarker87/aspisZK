from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2j-20261023'
norm=lambda s:re.sub(r'\s+','',s)
native=(R/'programs/r1-cost-probe/src/r1_pool_adapter.rs').read_text();probe=(E/'S2J-cut1/src/lib.rs').read_text();model=(D/'lean/S2E_Model.lean').read_text()
for i,local in [(2,'proof'),(3,'public'),(4,'checkpoint')]:
 assert norm(f'let {local}_account = &accounts[{i-2}];') in norm(native)
 assert norm(f'let {local}_account = &accounts[{i-2}];') in norm(probe)
body=native[native.index('    for (index, account)',native.index('fn require_distinct_accounts')):native.index('\n#[inline(never)]',native.index('fn require_distinct_accounts'))]
assert norm(body) in norm(probe)
for name in ['afterDistinct']:
 source=(D/'lean/S2J_Cut5.lean').read_text()
 suffix=model[model.index('        if proof.is_signer'):model.index('/-- [s2e_reference::S2E_Reference::proof_gate]')].strip()
 assert norm(suffix.replace('S2E_Reference.owned_data_len','_root_.S2E_Reference.S2E_Reference.owned_data_len')) in norm(source)
inputs=[R/'programs/r1-cost-probe/src/r1_pool_adapter.rs',D/'lean/S2E_Model.lean',E/'S2J-cut1/src/lib.rs']
(E/'S2J-continuation-source-pins.json').write_text(json.dumps({str(p.relative_to(R)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in inputs},indent=2)+'\n')
print('PASS: native cuts2-5 and verbatim extracted admission suffix')
