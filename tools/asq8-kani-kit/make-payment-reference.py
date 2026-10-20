#!/usr/bin/env python3
"""Generate a reviewed fixed-eight-word serializer copy; no shipped edits."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
p=root/'crates/aspis-statement/src/pool_v1/payment_relation.rs'
s=p.read_text()
def item(start,end):return s[s.index(start):s.index(end)]
out='''//! Extraction-only payment serialization. Validation stays the shipped validation.
//! The only arithmetic rewrite is the fixed-eight-word digest serialization.
use super::*;
use crate::pool_v1::{validate_pool_v1_private_transfer_public_v1,
    validate_pool_v1_withdrawal_public_v1};
use crate::pool_v1::payment_relation::{POOL_V1_PRIVATE_TRANSFER_STATEMENT_MAGIC,
    POOL_V1_WITHDRAWAL_STATEMENT_MAGIC, POOL_V1_PAYMENT_STATEMENT_VERSION,
    POOL_V1_CANONICAL_FEE};
'''
out+=item('const POOL_OFFSET:', '#[derive(Clone, Copy, Debug, PartialEq, Eq)]')
out+=item('#[derive(Clone, Copy)]\nstruct CommonPublicV1', '#[inline]\nfn digest_is_canonical')
out+=item('fn transfer_common(', 'pub fn validate_pool_v1_private_transfer_public_v1(')
out+=item('fn encode_common(', 'fn require_header(')
out=out.replace('encode_digest_canonical','digest_reference')
out+='\nfn digest_reference(digest: &Digest) -> [u8; 32] {\n'
for i in range(8):out+=f'    let b{i} = digest[{i}].0.to_le_bytes();\n'
out+='    [\n'+''.join('        '+', '.join(f'b{i}[{j}]' for j in range(4))+',\n' for i in range(8))+'    ]\n}\n'
(root/'crates/aspis-statement/src/pool_v1/asq8_payment_reference.rs').write_text(out)
