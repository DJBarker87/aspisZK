use std::{env, fs, os::unix::fs::PermissionsExt, path::PathBuf, str::FromStr};

use anyhow::{ensure, Context, Result};
use aspis_pool::{
    LEGACY_SPL_TOKEN_ACCOUNT_BYTES, LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES,
    LEGACY_SPL_TOKEN_PROGRAM_ID,
};
use base64::{engine::general_purpose::STANDARD as BASE64, Engine as _};
use serde::Deserialize;
use serde_json::json;
use sha2::{Digest as _, Sha256};
use solana_keypair::{read_keypair_file, Keypair};
use solana_message::{legacy, VersionedMessage};
use solana_program::{
    hash::Hash,
    instruction::{AccountMeta, Instruction},
    pubkey::Pubkey,
    system_instruction,
};
use solana_signer::Signer;
use solana_transaction::versioned::VersionedTransaction;

const DEVNET_GENESIS_HASH: &str = "EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG";

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Input {
    schema: String,
    genesis_hash: String,
    payer_keypair: String,
    source_authority_keypair: String,
    mint_keypair: String,
    source_token_keypair: String,
    destination_token_keypair: String,
    recent_blockhash: String,
    min_context_slot: u64,
    request_id: u64,
    mint_rent_lamports: u64,
    token_account_rent_lamports: u64,
    mint_amount: u64,
}

fn secure_keypair(path: &str, label: &str) -> Result<Keypair> {
    let metadata = fs::symlink_metadata(path).with_context(|| format!("stat {label}"))?;
    ensure!(
        metadata.file_type().is_file()
            && !metadata.file_type().is_symlink()
            && metadata.permissions().mode() & 0o077 == 0,
        "{label} must be a non-symlink regular file with no group/other permissions"
    );
    read_keypair_file(path).map_err(|error| anyhow::anyhow!("read {label}: {error}"))
}

fn initialize_mint(mint: Pubkey, authority: Pubkey) -> Instruction {
    // Canonical legacy SPL Token `InitializeMint2` encoding. `None` occupies
    // the fixed 36-byte COption<Pubkey> field; no Token-2022 extension exists.
    let mut data = Vec::with_capacity(70);
    data.push(20);
    data.push(0);
    data.extend_from_slice(authority.as_ref());
    data.extend_from_slice(&0_u32.to_le_bytes());
    data.extend_from_slice(&[0_u8; 32]);
    Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![AccountMeta::new(mint, false)],
        data,
    }
}

fn initialize_account(account: Pubkey, mint: Pubkey, authority: Pubkey) -> Instruction {
    let mut data = Vec::with_capacity(33);
    data.push(18); // Canonical legacy SPL Token `InitializeAccount3`.
    data.extend_from_slice(authority.as_ref());
    Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![
            AccountMeta::new(account, false),
            AccountMeta::new_readonly(mint, false),
        ],
        data,
    }
}

fn mint_to(mint: Pubkey, destination: Pubkey, authority: Pubkey, amount: u64) -> Instruction {
    let mut data = Vec::with_capacity(9);
    data.push(7); // Canonical legacy SPL Token `MintTo`.
    data.extend_from_slice(&amount.to_le_bytes());
    Instruction {
        program_id: LEGACY_SPL_TOKEN_PROGRAM_ID,
        accounts: vec![
            AccountMeta::new(mint, false),
            AccountMeta::new(destination, false),
            AccountMeta::new_readonly(authority, true),
        ],
        data,
    }
}

fn main() -> Result<()> {
    let input_path = PathBuf::from(
        env::args_os()
            .nth(1)
            .context("usage: build-public-devnet-token-fixture <input.json>")?,
    );
    ensure!(env::args_os().nth(2).is_none(), "unexpected extra argument");
    let input: Input = serde_json::from_slice(&fs::read(&input_path)?)?;
    ensure!(
        input.schema == "aspis.v7.public-devnet-token-fixture-input.v1"
            && input.genesis_hash == DEVNET_GENESIS_HASH
            && input.min_context_slot > 0
            && input.request_id > 0
            && input.mint_rent_lamports > 0
            && input.token_account_rent_lamports > 0
            && input.mint_amount > 0,
        "wrong schema, cluster, rent, or amount"
    );

    let payer = secure_keypair(&input.payer_keypair, "payer keypair")?;
    let authority = secure_keypair(&input.source_authority_keypair, "source authority keypair")?;
    let mint = secure_keypair(&input.mint_keypair, "mint keypair")?;
    let source = secure_keypair(&input.source_token_keypair, "source token keypair")?;
    let destination = secure_keypair(
        &input.destination_token_keypair,
        "destination token keypair",
    )?;
    let identities = [
        payer.pubkey(),
        authority.pubkey(),
        mint.pubkey(),
        source.pubkey(),
        destination.pubkey(),
    ];
    for left in 0..identities.len() {
        for right in left + 1..identities.len() {
            ensure!(identities[left] != identities[right], "fixture key alias");
        }
    }

    let instructions = vec![
        system_instruction::create_account(
            &payer.pubkey(),
            &mint.pubkey(),
            input.mint_rent_lamports,
            LEGACY_SPL_TOKEN_MINT_ACCOUNT_BYTES as u64,
            &LEGACY_SPL_TOKEN_PROGRAM_ID,
        ),
        initialize_mint(mint.pubkey(), authority.pubkey()),
        system_instruction::create_account(
            &payer.pubkey(),
            &source.pubkey(),
            input.token_account_rent_lamports,
            LEGACY_SPL_TOKEN_ACCOUNT_BYTES as u64,
            &LEGACY_SPL_TOKEN_PROGRAM_ID,
        ),
        initialize_account(source.pubkey(), mint.pubkey(), authority.pubkey()),
        system_instruction::create_account(
            &payer.pubkey(),
            &destination.pubkey(),
            input.token_account_rent_lamports,
            LEGACY_SPL_TOKEN_ACCOUNT_BYTES as u64,
            &LEGACY_SPL_TOKEN_PROGRAM_ID,
        ),
        initialize_account(destination.pubkey(), mint.pubkey(), authority.pubkey()),
        mint_to(
            mint.pubkey(),
            source.pubkey(),
            authority.pubkey(),
            input.mint_amount,
        ),
    ];
    let blockhash = Hash::from_str(&input.recent_blockhash).context("invalid blockhash")?;
    let message = VersionedMessage::Legacy(legacy::Message::new_with_blockhash(
        &instructions,
        Some(&payer.pubkey()),
        &blockhash,
    ));
    let transaction = VersionedTransaction::try_new(
        message,
        &[&payer, &authority, &mint, &source, &destination],
    )
    .map_err(|error| anyhow::anyhow!("sign token fixture transaction: {error}"))?;
    let wire = bincode::serialize(&transaction)?;
    ensure!(wire.len() < 1_232, "token fixture exceeds legacy envelope");
    let wire_base64 = BASE64.encode(&wire);
    println!(
        "{}",
        json!({
            "schema":"aspis.v7.public-devnet-token-fixture-signed-request.v1",
            "cluster":"devnet",
            "genesisHash":DEVNET_GENESIS_HASH,
            "payer":payer.pubkey().to_string(),
            "sourceAuthority":authority.pubkey().to_string(),
            "mint":mint.pubkey().to_string(),
            "sourceTokenAccount":source.pubkey().to_string(),
            "destinationTokenAccount":destination.pubkey().to_string(),
            "mintAmount":input.mint_amount,
            "serializedTransactionBytes":wire.len(),
            "signedWireSha256":format!("{:x}", Sha256::digest(&wire)),
            "signature":transaction.signatures[0].to_string(),
            "simulationRequest":{
                "jsonrpc":"2.0","id":input.request_id,"method":"simulateTransaction",
                "params":[wire_base64,{"encoding":"base64","commitment":"confirmed",
                    "sigVerify":true,"replaceRecentBlockhash":false,
                    "minContextSlot":input.min_context_slot}]
            },
            "sendRequest":{
                "jsonrpc":"2.0","id":input.request_id+100_000,"method":"sendTransaction",
                "params":[wire_base64,{"encoding":"base64","skipPreflight":true,
                    "preflightCommitment":"confirmed","maxRetries":0,
                    "minContextSlot":input.min_context_slot}]
            }
        })
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn legacy_token_encodings_are_canonical_and_fixed_width() {
        let mint = Pubkey::new_unique();
        let account = Pubkey::new_unique();
        let authority = Pubkey::new_unique();
        let initialize_mint = initialize_mint(mint, authority);
        assert_eq!(initialize_mint.program_id, LEGACY_SPL_TOKEN_PROGRAM_ID);
        assert_eq!(initialize_mint.data.len(), 70);
        assert_eq!(initialize_mint.data[0], 20);
        assert_eq!(initialize_mint.data[1], 0);
        assert_eq!(&initialize_mint.data[2..34], authority.as_ref());
        assert_eq!(&initialize_mint.data[34..], &[0_u8; 36]);

        let initialize_account = initialize_account(account, mint, authority);
        assert_eq!(initialize_account.data.len(), 33);
        assert_eq!(initialize_account.data[0], 18);
        assert_eq!(&initialize_account.data[1..], authority.as_ref());

        let mint_to = mint_to(mint, account, authority, 1_000);
        assert_eq!(mint_to.data, [vec![7], 1_000_u64.to_le_bytes().to_vec()].concat());
        assert!(mint_to.accounts[2].is_signer);
    }
}
