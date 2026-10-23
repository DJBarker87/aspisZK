from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[6]
E=Path(__file__).resolve().parent.parent
s=(R/'crates/aspis-core/src/state_only_hiding.rs').read_text()
a=s.index('    pub fn encode(self)');b=s.index('\n}\n',a)
t=(R/'crates/aspis-prover/src/state_only_hiding.rs').read_text()
c=t.index('fn derive_state_only_mask_seed_from_entropy_ref(');d=t.index('\npub fn build_state_only_mask_material',c)
copy=(E/'native/source.rs').read_text()
assert s[a:b] in copy and t[c:d] in copy
for constant in ['aspis:state-only:private-mask-seed:v1']:
 assert constant in t and constant in copy
record={'exact_body_identity':['StateOnlyHidingContext::encode','derive_state_only_mask_seed_from_entropy_ref'], 'source_sha256':hashlib.sha256(copy.encode()).hexdigest()}
(E/'body-identity.json').write_text(json.dumps(record,indent=2)+'\n')
print(record)
