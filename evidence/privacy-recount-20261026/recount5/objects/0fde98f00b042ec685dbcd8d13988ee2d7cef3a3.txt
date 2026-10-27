# N7 boundary inventory (candidate 0c9dc9a4cc)

The request does **not** contain private witness integers. This corrects the task premise using the actual planner and the corrected D272 audit.

| Boundary field | Type / size | Current encoding | Classification |
|---|---|---|---|
| keys | list of path strings, public count; paths variable length | JSON strings | public metadata; paths locate retained key files |
| each key file, bytes 0..31 | Ed25519 seed, 32 bytes | JSON decimal u8 array | secret signing key; N7 |
| each key file, bytes 32..63 | Ed25519 public key, 32 bytes | same 64-element JSON decimal array | public; proposed transport keeps full keypair as one fixed 64-byte record |
| instructions | list; program address 32 bytes, accounts (address32, signer bool, writable bool), variable data | base58 strings / bools / lowercase hex data | public transaction |
| blockhash | 32 bytes | base58 JSON string | public |
| action, note, withdrawal, genesis, sequence, activation_slot | string / u64 narrowed to u32 note / bool / bool / u64 / u64 | JSON primitives | public fixture and operation selectors |
| pool, mint, payer, registry, verifier, funding_payer, governance, source, token_owner, destination, checkpoint, public_account, verifier_checkpoint | 32-byte addresses | base58 strings | public |
| registry_hash, verifier_hash | each 32 bytes | hex strings | public release hashes |
| lane_bytes | [u8;768] lane state | 1536 hex characters | public chain state |
| checkpoint_bytes | [u8;192] checkpoint | 384 hex characters | public chain state |
| marker_bytes | [u8;208] nullifier marker | 416 hex characters | public chain state |
| candidate_bytes | [u8;688] verified afterstate | 1376 hex characters | public chain state |
| proof_accounts | exactly eight 32-byte addresses | base58 JSON strings | public; nonce callback uses their raw 32 bytes |
| proof_dir | filesystem path string | JSON string | public shape/storage metadata; contents sensitive |

`Client64_proof_accounts.py` retains eight key files and manifests but passes only their public addresses and public identity/snapshot fields to action=prove. No secret key in its prover request. The signing route later uses retained key paths via r1_devnet_spend.py invoke/send.

## Secrets constructed inside Rust, not supplied over Python→Rust

`plan::note/digest` constructs input nullifier key and salt (Digest = 8 M31 limbs, 32 canonical bytes each), value u64=1000, pair leaf and depth-20 membership siblings (20×32 bytes), index u32, three super-root siblings (3×32 bytes), and three Boolean directions. Output recipient/change owner keys and salts are Digests (32 bytes each) and values u64 (600/400 or 750). These are deterministic **public fixtures** selected by public note/withdrawal; they would be witness secrets in a real wallet. No caller-supplied decimal witness exists here.

Private leaf salts, mask seed/material, entropy and mask-nonce durable state are generated/derived inside the prover. None is a Python request field. Proof-account nonce is public 32-byte account address, not private mask entropy. Recovery files written by Rust contain note key/salt hex and decimal values; this is Rust→disk, not Rust input parsing, and needs a separate storage/observer treatment.

No wallet/key file was read for this inventory. No theorem or premise is changed. Target not yet established.
