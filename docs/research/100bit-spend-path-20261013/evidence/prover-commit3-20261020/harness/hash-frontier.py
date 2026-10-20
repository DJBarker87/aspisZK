#!/usr/bin/env python3
"""Read-only source checks for the callback/Poseidon backend mismatch.
Run from repository root. This is a source inventory, not a Kani certificate.
"""
import hashlib,json,subprocess
from pathlib import Path
R=Path.cwd()
checks={
 'hash_fn_byte_interface':('crates/aspis-core/src/transcript.rs','pub type HashFn = fn(&[&[u8]]) -> [u8; 32];'),
 'host_hash_implementation':('crates/aspis-prover/src/lib.rs','''pub fn host_hashv(inputs: &[&[u8]]) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for input in inputs {
        hasher.update(input);
    }
    hasher.finalize().into()
}'''),
 'host_hash_selection':('crates/aspis-prover/src/lib.rs','pub const HOST_HASH: HashFn = host_hashv;'),
 'fixture_hash_import':('crates/aspis-r1-cost-probe/examples/masked_fixture_gate.rs','use aspis_prover::HOST_HASH;'),
 'fixture_hash_selection':('crates/aspis-r1-cost-probe/examples/masked_fixture_gate.rs','let hash: HashFn = HOST_HASH;'),
 'retry_hash_selection':('crates/aspis-r1-cost-probe/examples/r1p_retry_gate.rs','prover::prove_masked_attempt(fixture.public(), &fixture.compiled, Variant::S2, HOST_HASH, secrets, &mut ledger)'),
 'shipped_digest_backend':('programs/r1-cost-probe/src/lib.rs','''fn digest(&self, parts: &[&[u8]]) -> [u8; 32] {
        hashv(parts).to_bytes()
    }'''),
 'poseidon_field_interface':('crates/aspis-statement/src/poseidon2.rs','pub fn permute_optimized(state: &mut [M31; 16])'),
 'poseidon_compression_interface':('crates/aspis-statement/src/poseidon2.rs','pub fn merkle_node_compress_v3(left: &Digest, right: &Digest) -> Digest'),
 'poseidon_digest_type':('crates/aspis-statement/src/poseidon2.rs','pub type Digest = [M31; DIGEST_ELEMS];'),
 'mask_seed_calls_callback':('crates/aspis-prover/src/state_only_hiding.rs','''Ok(hash(&[
        MASK_SEED_DOMAIN,
        &precommit_binding,
        &context.encode(),
        private_entropy,
    ]))'''),
 'leaf_salt_calls_callback':('crates/aspis-prover/src/state_only_entropy.rs','''Ok(hash(&[
            LEAF_SALT_DOMAIN,
            &attempt_binding,
            &self.mask_nonce,
            &[tree_tag],
            &leaf_index.to_le_bytes(),
            self.leaf_salt_seed.as_ref(),
        ]))'''),
}
result={'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'kind':'read-only exact source-span inventory; no solver/Lean claim','checks':{}}
for name,(path,needle) in checks.items():
    data=(R/path).read_bytes();text=data.decode();assert needle in text,name
    result['checks'][name]={'path':path,'sha256':hashlib.sha256(data).hexdigest(),'line':text[:text.index(needle)].count('\n')+1,'verbatim':needle,'found':True}
for path in ['crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-prover/src/state_only_hiding.rs']:
    text=(R/path).read_text();assert 'poseidon2' not in text and 'permute_optimized' not in text
result['conclusion']='D90 Poseidon field permutation/compression equality does not identify the SHA-256 callback in the prover seed/salt/expander cone. No Poseidon-to-byte-HashFn bridge has been supplied or proved.'
result['stage_1']='blocked: requested admitted backend differs from the actual callback backend; no arbitrary output model or stub installed'
print(json.dumps(result,indent=2))
