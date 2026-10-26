#!/usr/bin/env python3
"""Copy exact production entropy source fragments into a tiny no-stub probe."""
from pathlib import Path
import hashlib,json,sys
root=Path(__file__).resolve().parents[3]
source=root/'crates/aspis-prover/src/state_only_entropy.rs'
text=source.read_text()
def block(start):
    first=text.index(start)
    opening=text.index('{',first)
    level=1; end=opening+1
    while level:
        level += (text[end]=='{')-(text[end]=='}'); end+=1
    return text[first:end]
parts=[block('pub enum StateOnlyAttemptEntropyError'),
       block('pub struct StateOnlyAttemptSecrets'),
       block('fn entropy_nonzero32'),
       block('    pub fn generate_for_mask_nonce(')]
output='use zeroize::Zeroizing;\nconst ENTROPY_RETRY_LIMIT: usize = 16;\n'+ '\n'.join(parts[:3])+'\nimpl StateOnlyAttemptSecrets {\n'+parts[3]+'\n}\n'
# Exactly the production ? conversion, retained verbatim.
conversion=block('impl From<getrandom::Error> for StateOnlyAttemptEntropyError')
output+=conversion+'\n'
output+='''fn main() {
    // A public, fixed non-wallet nonce. No account or key is created.
    let nonce = [1u8; 32];
    let first = match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
        Ok(value) => value, Err(_) => panic!("native first call failed") };
    let second = match StateOnlyAttemptSecrets::generate_for_mask_nonce(nonce) {
        Ok(value) => value, Err(_) => panic!("native second call failed") };
    assert_eq!(first.mask_nonce, nonce);
    assert_eq!(second.mask_nonce, nonce);
    let distinct = first.field_mask_entropy != second.field_mask_entropy ||
        first.leaf_salt_seed != second.leaf_salt_seed;
    assert!(distinct, "native successive successful outputs coincided");
    println!("same_public_nonce=true native_successes=2 private_output_distinct=true");
    // Zeroizing owns both private seeds. No entropy bytes or hashes are logged.
}
'''
out=Path(__file__).resolve().parent
manifest={'production_source':str(source.relative_to(root)),
 'production_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'fragments_sha256':[hashlib.sha256(s.encode()).hexdigest() for s in parts+[conversion]],
 'probe_sha256':hashlib.sha256(output.encode()).hexdigest(),
 'source_fragments_verbatim':True,'stubs':False,'logged_private_bytes':False,
 'scope':'native entropy helper only; not full prover, SBF, privacy or compiler adequacy'}
if '--check' in sys.argv:
    assert (out/'main.rs').read_text() == output
    assert json.loads((out/'source-pins.json').read_text()) == manifest
    print('source fragments and probe pins match')
else:
    (out/'main.rs').write_text(output)
    (out/'source-pins.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest))
