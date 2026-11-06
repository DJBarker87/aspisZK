"""One-shot, frozen-input source surgery; NKX_source.py independently audits it."""
from NKX_source import *
def write(p,b): (R/p).write_bytes(b)
def name(b,n):
 q=n.child_by_field_name('name');return b[q.start_byte:q.end_byte].decode() if q else ''
def drop(p,names):
 b=(R/p).read_bytes();root=parse(b);write(p,remove_nodes(b,[n for n in root.named_children if name(b,n) in names]))
def replace_tests(p,keep,extra=b''):
 b=(R/p).read_bytes();root=parse(b)
 n=next(n for n in root.named_children if n.type=='mod_item' and name(b,n)=='tests')
 body=n.child_by_field_name('body');parts=[]
 for c in body.named_children:
  if c.type=='function_item' and name(b,c) in keep:parts.append(b'    #[test]\n'+b[c.start_byte:c.end_byte])
 new=b'#[cfg(test)]\nmod tests {\n    use super::*;\n'+b'\n'.join(parts)+extra+b'\n}\n'
 start=n.prev_named_sibling.start_byte if n.prev_named_sibling.type=='attribute_item' else n.start_byte
 write(p,b[:start]+new+b[n.end_byte:])
p='programs/aspis-pool/src/processor.rs';b=(R/p).read_bytes();root=parse(b)
keep={'solana_sha256','supported_program_loader','require_unique_accounts','require_payer_and_system_program','close_program_account_v1','plan_fresh_program_pda','create_or_allocate_pda','create_or_allocate_pda_with_rent','create_or_allocate_with_seed_with_rent','require_token_program_account','require_initialized_empty_vault','plan_vault_initialization','initialize_vault_account','create_pair_forest_nullifier_marker_if_needed_v1','process_instruction','require_transaction_level_invocation_v1'}
remove=[n for n in root.named_children if n.type=='function_item' and name(b,n) not in keep or n.type=='struct_item' and name(b,n)!='SolanaPoolCpiRuntimeV1']
b=remove_nodes(b,remove)
# Retain every byte of the AS8*/ASQ8/ASF8 and ASJP/ASJW dispatcher arms.
start=b.index(b'    } else if magic == POOL_V1_INITIALIZE_INSTRUCTION_MAGIC')
end=b.index(b'    } else if cfg!(feature = "pair-afterstate-evidence")',start)
b=b[:start]+b[end:]
start=b.index(b'    } else if magic == POOL_V1_PRIVATE_TRANSFER_INSTRUCTION_MAGIC')
end=b.index(b'    } else {\n        Err(ProgramError::InvalidInstructionData)',start)
b=b[:start]+b[end:]
# Replace imports only; all retained function items are untouched.
start=b.index(b'use crate::{');end=b.index(b'\n#[cfg(feature = "pair-afterstate-evidence")]',start)
b=b[:start]+b'''use crate::{
    error::PoolV1ProgramError,
    history::require_program_account,
    nullifier::NullifierMarkerPreparationV1,
    vault::{parse_legacy_token_account_v1, pool_v1_vault_authority_address,
        pool_v1_vault_token_account_address, LEGACY_SPL_TOKEN_ACCOUNT_BYTES,
        LEGACY_SPL_TOKEN_PROGRAM_ID, POOL_V1_VAULT_TOKEN_ACCOUNT_SEED},
};
'''+b[end:]
write(p,b)
replace_tests(p,{'public_dispatch_rejects_short_and_unknown_instruction_headers','transaction_level_gate_rejects_every_cpi_stack_height'},b'''
    #[test]
    fn removed_legacy_instruction_magics_are_rejected() {
        let program_id = Pubkey::new_unique();
        for magic in [b"ASIN", b"ASDI", b"ASPT", b"ASWD", b"ASPP", b"ASPF", b"ASPX"] {
            for length in [4usize, 184, 512, 1880] {
                let mut bytes = std::vec![0u8; length];
                bytes[..4].copy_from_slice(magic);
                assert_eq!(process_instruction(&program_id, &[], &bytes),
                    Err(ProgramError::InvalidInstructionData), "{:?}, length {}", magic, length);
            }
        }
    }
''')
# Exclusive legacy modules: source imports show no pair-* dependency on them.
removed_modules=['cancel_prepared_settlement_instruction','prepared_settlement','prepared_settlement_format','prepared_settlement_instruction','settle_prepared_instruction','transition','anchor']
for m in removed_modules:(R/('programs/aspis-pool/src/'+m+'.rs')).unlink()
# Shared data-only request and initialization types retain their frozen text.
for m,ty,imports in [('deposit','DepositRequestV1',b'use aspis_statement::poseidon2::Digest;\n'),('state','PoolInitializationV1',b'use aspis_core::field::M31;\nuse aspis_statement::pool_v1::VerifierPolicyV1;\n')]:
 p='programs/aspis-pool/src/'+m+'.rs';b=(R/p).read_bytes();n=next(n for n in parse(b).named_children if n.type=='struct_item' and name(b,n)==ty);start=n.prev_named_sibling.start_byte
 write(p,b'//! Shared pair-forest initialization/request data.\n\n'+imports+b'\n'+b[start:n.end_byte]+b'\n')
# Keep the shared AS8D encoder/strict parameterized decoder, remove ASDI entry APIs.
p='programs/aspis-pool/src/deposit_transport.rs';b=(R/p).read_bytes();root=parse(b)
keep={'digest_is_canonical','encode_deposit_instruction_v1','decode_deposit_instruction_with_magic_v1'}
b=remove_nodes(b,[n for n in root.named_children if n.type=='function_item' and name(b,n) not in keep or n.type=='struct_item' and name(b,n)=='DepositEventReturnDataV1' or n.type=='impl_item' and b'DepositEventReturnDataV1' in b[n.start_byte:n.end_byte] or n.type=='mod_item'])
start=b.index(b'use crate::{');end=b.index(b'\n\npub const',start);b=b[:start]+b'use crate::deposit::DepositRequestV1;'+b[end:];write(p,b)
# Single-tree wrappers; identity-based planners are shared by retained routes.
drop('programs/aspis-pool/src/vault.rs',{'plan_legacy_deposit_transfer_v1','plan_legacy_withdrawal_transfer_v1'})
p=R/'programs/aspis-pool/src/vault.rs';b=p.read_bytes().replace(b'use crate::{error::PoolV1ProgramError, state::PoolStateV1};',b'use crate::error::PoolV1ProgramError;');p.write_bytes(b)
# Legacy public decoders/init codecs; pair codecs and their common encoding helpers remain exact.
drop('programs/aspis-pool/src/instruction.rs',{'encode_initialize_instruction_v1','decode_initialize_instruction_v1','decode_private_transfer_instruction_v1','decode_withdrawal_instruction_v1','decode_deposit_top_level_v1','encode_initialization_receipt_v1'})
p=R/'programs/aspis-pool/src/instruction.rs';b=p.read_bytes().replace(b'deposit_transport::{decode_deposit_instruction_v1, DepositInstructionFormatErrorV1}',b'deposit_transport::DepositInstructionFormatErrorV1');p.write_bytes(b)
# These tests exercised removed public decoders exclusively. Pair processors retain full integration tests.
p='programs/aspis-pool/src/instruction.rs';b=(R/p).read_bytes();write(p,remove_nodes(b,[n for n in parse(b).named_children if n.type=='mod_item' and name(b,n)=='tests']))
(R/'programs/aspis-pool/tests/payment_relation_abi.rs').unlink()
# Exports: remove deleted APIs, preserving shared names used by unchanged modules.
p=R/'programs/aspis-pool/src/lib.rs';b=p.read_text()
import re
for m in removed_modules:
 b=re.sub(r'pub(?:\(crate\))? mod '+m+r';\n','',b)
 b=re.sub(r'pub use '+m+r'::\{.*?\};\n','',b,flags=re.S)
b=b.replace('pub use deposit::{apply_vault_backed_deposit_v1, DepositRequestV1};','pub use deposit::DepositRequestV1;').replace('pub use deposit_transport::process_vault_backed_deposit_instruction_v1;\n','')
b=re.sub(r'pub use state::\{.*?\};', 'pub use state::PoolInitializationV1;',b,flags=re.S)
for s in ['decode_initialize_instruction_v1, ','decode_private_transfer_instruction_v1,','decode_withdrawal_instruction_v1, ','encode_initialize_instruction_v1,'] :b=b.replace(s,'')
p.write_text(b)
