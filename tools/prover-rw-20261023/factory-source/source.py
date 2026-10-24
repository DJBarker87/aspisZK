"""Prospective production fission only; no semantic equivalence claim."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
R=D.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
original=(D.parent/'factory-iteration/production-source.txt').read_bytes()
actual=(R/'crates/aspis-prover/src/state_only_entropy.rs').read_bytes()
assert actual==original, 'preflight requires unchanged original production source'
cut=(D.parent/'factory-iteration/proof-cut/selected.rs').read_text()
assert sha(cut.encode())=='6ca3b19a9adb83aff665142323538041b92016df7eb44640599d9102d82c3455'
helper=cut[cut.index('    pub fn one_draw('):cut.rindex('\n}')]
private=helper.replace('    pub fn one_draw(', '    fn one_draw(', 1)
old=original.decode()
start=old.index('    pub fn generate_for_mask_nonce(')
end=old.index('\n    pub fn mask_nonce(',start)
before=old[start:end]
controller=before[:before.index('        while retry<limit {')]+'        while retry<limit {\n            let (next_retry, owner) = Self::one_draw(mask_nonce, retry)?;\n            match owner {\n                Some(owner) => return Ok(owner),\n                None => retry = next_retry,\n            }\n        }\n        Err(StateOnlyAttemptEntropyError::RepeatedZeroBlock)\n    }\n'
prefix=cut[:cut.index('impl StateOnlyAttemptSecrets {')]
selected=prefix+'impl StateOnlyAttemptSecrets {\n'+controller+'\n'+private+'\n}\n'
proposal=old[:start]+controller+'\n'+private+'\n'+old[end:]
outputs={D/'preflight/lib.rs':selected.encode(),D/'proposed-state-only-entropy.rs.txt':proposal.encode()}
meta=dict(schema='ProverRwFactorySource-prospective-source-v1',original_sha256=sha(original),original_factory_span=dict(start_byte=start,end_byte=end,sha256=sha(before.encode())),cut056_sha256=sha(cut.encode()),helper_before=helper,helper_after=private,controller_before=before,controller_after=controller,prospective_full_source_sha256=sha(proposal.encode()),selected_sha256=sha(selected.encode()),production_edited=False,claim='exact prospective factoring/visibility association; not Rust/MIR semantics or actual source progress')
for p,b in outputs.items():
 if '--check' in sys.argv: assert p.read_bytes()==b,p
 else:p.write_bytes(b)
p=D/'source-map.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
print('prospective source association checked; production unchanged')
