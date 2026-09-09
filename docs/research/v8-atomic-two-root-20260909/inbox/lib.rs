//! Inactive research program. B is a message inbox, never a value ledger.
#![allow(unexpected_cfgs)]
use aspis_statement::{
    encode_digest_canonical,
    pool_v1::{
        decode_pool_v1_nullifier_marker, decode_pool_v1_pair_forest_master_v1,
        decode_pool_v1_pair_forest_terminal_request_v1, PoolV1PairForestTerminalPaymentV1,
        POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES,
    },
};
use solana_program::{
    account_info::AccountInfo,
    entrypoint::ProgramResult,
    hash::hashv,
    instruction::AccountMeta,
    program::{invoke, invoke_signed, set_return_data},
    program_error::ProgramError,
    pubkey::Pubkey,
    rent::Rent,
    system_instruction, system_program,
    sysvar::Sysvar,
};

solana_program::entrypoint!(entry);
#[cfg(target_os = "solana")]
#[global_allocator]
static ALLOC: solana_program::entrypoint::BumpAllocator =
    solana_program::entrypoint::BumpAllocator {
        start: solana_program::entrypoint::HEAP_START_ADDRESS as usize,
        len: 256 * 1024,
    };

pub const ID: Pubkey = Pubkey::new_from_array([0xb8; 32]);
pub const POOL: Pubkey = Pubkey::new_from_array([0x41; 32]);
pub const VERIFIER: Pubkey =
    solana_program::pubkey!("7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue");
pub const DOMAIN: &[u8] = b"aspis/research/v8/atomic-message/v1";
pub const NODE: &[u8] = b"aspis/research/v8/atomic-message/v1/node";
pub const RELEASE_PREIMAGE: &[u8] =
    b"aspis/research/v8/atomic-message/v1/release:pool-asq8:sha256-depth20:message-only";
pub const STATE_BYTES: usize = 116;
pub const REQUEST_BYTES: usize = 1112;
pub const HEADER: &[u8; 8] = b"BIX8\x01\x14\0\0";
pub const SEED: &[u8] = b"aspis-v8-inbox-v1";
const PROFILE: [u8; 32] = [
    121, 147, 51, 56, 96, 194, 205, 16, 170, 24, 62, 117, 31, 39, 16, 186, 39, 155, 51, 42, 187,
    191, 221, 206, 119, 59, 50, 23, 103, 240, 1, 186,
];
const V8_RELEASE: [u8; 32] = [
    151, 98, 227, 119, 25, 209, 243, 34, 243, 255, 11, 167, 44, 210, 163, 48, 184, 241, 130, 119,
    107, 226, 91, 66, 45, 195, 131, 11, 66, 206, 145, 255,
];
fn reject() -> ProgramError {
    ProgramError::InvalidInstructionData
}
fn check(ok: bool) -> ProgramResult {
    if ok {
        Ok(())
    } else {
        Err(reject())
    }
}
fn word(data: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(data[at..at + 8].try_into().unwrap())
}
pub fn empty() -> [u8; 32] {
    hashv(&[DOMAIN, b"/empty"]).to_bytes()
}
pub fn parent(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
    hashv(&[NODE, a, b]).to_bytes()
}
pub fn address(master: &Pubkey, asset: u32) -> (Pubkey, u8) {
    Pubkey::find_program_address(&[SEED, master.as_ref(), &asset.to_le_bytes()], &ID)
}
// Raw snapshot is only accepted after the pinned Pool has canonically decoded
// these exact bytes in its CPI. These offsets are checked against the full
// source encoder by the differential driver. No independent authority is granted.
fn lane_snapshot(a: &AccountInfo) -> Result<(u64, [u8; 32]), ProgramError> {
    check(a.owner == &POOL && !a.executable && !a.is_signer && a.is_writable)?;
    let d = a.try_borrow_data()?;
    check(d.len() == POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES)?;
    Ok((word(&d, 88), d[96..128].try_into().unwrap()))
}
fn initialize(accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    check(data.len() == 44 && &data[..8] == b"ABI8\x01\x14\0\0" && accounts.len() == 4)?;
    let (inbox, payer, system, master) = (&accounts[0], &accounts[1], &accounts[2], &accounts[3]);
    check(
        master.key.as_ref() == &data[8..40]
            && master.owner == &POOL
            && !master.is_writable
            && !master.is_signer
            && !master.executable,
    )?;
    let m =
        decode_pool_v1_pair_forest_master_v1(&master.try_borrow_data()?).map_err(|_| reject())?;
    let asset = u32::from_le_bytes(data[40..44].try_into().unwrap());
    check(m.identity.asset_id.0 == asset)?;
    let expected_master = Pubkey::find_program_address(
        &[b"aspis-pair-forest-master-v1", &m.identity.asset_mint],
        &POOL,
    )
    .0;
    check(master.key == &expected_master)?;
    let (key, bump) = address(master.key, asset);
    check(
        inbox.key == &key
            && inbox.is_writable
            && !inbox.is_signer
            && !inbox.executable
            && inbox.owner == &system_program::id()
            && inbox.data_is_empty(),
    )?;
    check(
        payer.is_signer
            && payer.is_writable
            && system.key == &system_program::id()
            && system.executable,
    )?;
    let asset_bytes = asset.to_le_bytes();
    let bump_bytes = [bump];
    let seeds: &[&[u8]] = &[SEED, master.key.as_ref(), &asset_bytes, &bump_bytes];
    let rent = Rent::get()?.minimum_balance(STATE_BYTES);
    if inbox.lamports() < rent {
        invoke(
            &system_instruction::transfer(payer.key, inbox.key, rent - inbox.lamports()),
            &[payer.clone(), inbox.clone(), system.clone()],
        )?;
    }
    invoke_signed(
        &system_instruction::allocate(inbox.key, STATE_BYTES as u64),
        &[inbox.clone(), system.clone()],
        &[seeds],
    )?;
    invoke_signed(
        &system_instruction::assign(inbox.key, &ID),
        &[inbox.clone(), system.clone()],
        &[seeds],
    )?;
    let mut root = empty();
    for _ in 0..20 {
        root = parent(&root, &root);
    }
    let mut d = inbox.try_borrow_mut_data()?;
    d.fill(0);
    d[..8].copy_from_slice(HEADER);
    d[8..40].copy_from_slice(master.key.as_ref());
    d[40..44].copy_from_slice(&asset_bytes);
    d[52..84].copy_from_slice(&root);
    Ok(())
}

fn settle(accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    check(
        data.len() == REQUEST_BYTES
            && (&data[..8] == b"ATH8\x01\x14\0\0" || &data[..8] == b"ATF8\x01\x14\0\0"),
    )?;
    check(accounts.len() == 14 || accounts.len() == 15)?;
    let n = accounts.len() - 3;
    let pool = &accounts[n];
    let inbox = &accounts[n + 1];
    let instructions = &accounts[n + 2];
    check(pool.key == &POOL && pool.executable && !pool.is_writable && !pool.is_signer)?;
    check(inbox.owner == &ID && inbox.is_writable && !inbox.is_signer && !inbox.executable)?;
    check(
        instructions.key == &solana_program::sysvar::instructions::id()
            && !instructions.is_writable
            && !instructions.is_signer,
    )?;
    for (i, a) in accounts.iter().enumerate() {
        check(!accounts[..i].iter().any(|b| a.key == b.key))?;
    }
    // Fixed local choreography; the runtime authenticates the instructions
    // sysvar. Both B instructions carry identical bytes apart from the phase.
    // Thus a successful precheck necessarily has a later failing-or-settling B
    // instruction in THIS transaction. No persistent prepare/cleanup state.
    let phase = data.starts_with(b"ATF8");
    let current = solana_program::sysvar::instructions::load_current_index_checked(instructions)?;
    check(current == if phase { 2 } else { 0 })?;
    let pre = solana_program::sysvar::instructions::load_instruction_at_checked(0, instructions)?;
    let source =
        solana_program::sysvar::instructions::load_instruction_at_checked(1, instructions)?;
    let final_ix =
        solana_program::sysvar::instructions::load_instruction_at_checked(2, instructions)?;
    check(
        pre.program_id == ID
            && final_ix.program_id == ID
            && source.program_id == POOL
            && pre.data.len() == REQUEST_BYTES
            && final_ix.data.len() == REQUEST_BYTES
            && &pre.data[..4] == b"ATH8"
            && &final_ix.data[..4] == b"ATF8"
            && pre.data[4..] == data[4..]
            && final_ix.data[4..] == data[4..]
            && source.data == data[792..],
    )?;
    let metas: Vec<_> = accounts
        .iter()
        .map(|a| {
            if a.is_writable {
                AccountMeta::new(*a.key, a.is_signer)
            } else {
                AccountMeta::new_readonly(*a.key, a.is_signer)
            }
        })
        .collect();
    check(pre.accounts == metas && final_ix.accounts == metas && source.accounts == metas[..n])?;
    let request =
        decode_pool_v1_pair_forest_terminal_request_v1(&data[792..]).map_err(|_| reject())?;
    let public = match request.public {
        PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p) => p,
        _ => return Err(reject()),
    };
    check(
        request.pool_program == POOL.to_bytes()
            && request.verifier_profile == PROFILE
            && request.verifier_release == V8_RELEASE,
    )?;
    check(
        accounts[n - 2].key == &VERIFIER
            && accounts[n - 2].executable
            && !accounts[n - 2].is_writable
            && !accounts[n - 2].is_signer,
    )?;
    check(
        public.pool == accounts[0].key.to_bytes()
            && inbox.key == &address(accounts[0].key, public.asset_id.0).0,
    )?;
    let bseq = word(data, 8);
    check(bseq < 1 << 20)?;
    {
        let d = inbox.try_borrow_data()?;
        check(
            d.len() == STATE_BYTES
                && &d[..8] == HEADER
                && d[8..40] == public.pool
                && d[40..44] == public.asset_id.0.to_le_bytes()
                && word(&d, 44) == bseq
                && d[52..84] == data[16..48],
        )?;
    }
    let aseq = word(data, 80);
    let aroot: [u8; 32] = data[88..120].try_into().unwrap();
    if !phase {
        let snapshot = lane_snapshot(&accounts[2])?;
        check(snapshot == (aseq, aroot))?;
        return Ok(());
    }
    // At index 2, index 1 has successfully executed the PINNED Pool's full
    // ASQ8 -> ASF8 -> verifier -> authenticated ASR8 -> settlement path.
    // Read its canonical published marker, not cross-instruction return data.
    let marker_account = &accounts[n - 7];
    check(
        marker_account.owner == &POOL
            && marker_account.is_writable
            && !marker_account.is_signer
            && !marker_account.executable,
    )?;
    let marker = decode_pool_v1_nullifier_marker(&marker_account.try_borrow_data()?)
        .map_err(|_| reject())?;
    let canonical_nullifier = encode_digest_canonical(&public.nullifier);
    let marker_key = Pubkey::find_program_address(
        &[
            b"aspis-pool-nullifier-v1",
            &public.pool,
            &canonical_nullifier,
        ],
        &POOL,
    )
    .0;
    check(
        marker_account.key == &marker_key
            && marker.pool == public.pool
            && marker.nullifier == public.nullifier
            && marker.deployment_domain == public.deployment_domain
            && marker.verifier_profile == PROFILE
            && marker.verifier_release == V8_RELEASE
            && marker.transition_kind == request.public.transition_kind()
            && marker.retained_anchor_sequence == public.anchor_sequence
            && marker.retained_anchor_root == public.anchor_root,
    )?;
    let (next_seq, next_root) = lane_snapshot(&accounts[2])?;
    check(next_seq == aseq.checked_add(1).ok_or_else(reject)?)?;
    solana_program::msg!("atomic:A-settled-real-pool");
    let release = hashv(&[RELEASE_PREIMAGE]).to_bytes();
    let leaf = hashv(&[
        DOMAIN,
        &release,
        ID.as_ref(),
        POOL.as_ref(),
        VERIFIER.as_ref(),
        accounts[0].key.as_ref(),
        accounts[2].key.as_ref(),
        accounts[n - 1].key.as_ref(),
        &aseq.to_le_bytes(),
        &aroot,
        &next_seq.to_le_bytes(),
        &next_root,
        inbox.key.as_ref(),
        &bseq.to_le_bytes(),
        &data[16..48],
        &data[792..],
    ])
    .to_bytes();
    check(leaf == data[120..152])?;
    let mut old = empty();
    let mut new = leaf;
    let mut index = bseq;
    for sibling in data[152..792].chunks_exact(32) {
        let sibling: &[u8; 32] = sibling.try_into().unwrap();
        if index & 1 == 0 {
            old = parent(&old, sibling);
            new = parent(&new, sibling);
        } else {
            old = parent(sibling, &old);
            new = parent(sibling, &new);
        }
        index >>= 1;
    }
    check(old == data[16..48] && new == data[48..80])?;
    // The only intervening instruction is the exact source Pool settlement;
    // its account list omits B, so it cannot mutate the destination state.
    let mut d = inbox.try_borrow_mut_data()?;
    check(word(&d, 44) == bseq && d[52..84] == old)?;
    d[44..52].copy_from_slice(&(bseq + 1).to_le_bytes());
    d[52..84].copy_from_slice(&new);
    d[84..116].copy_from_slice(&leaf);
    solana_program::log::sol_log_data(&[b"atomic:receipt-v1", &leaf, &new]);
    set_return_data(&leaf);
    Ok(())
}
pub fn entry(id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    check(id == &ID)?;
    if data.starts_with(b"ABI8") {
        initialize(accounts, data)
    } else {
        settle(accounts, data)
    }
}
