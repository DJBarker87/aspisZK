# Deployment SOL recovery policy (owner instruction, 2026-10-29)

Owner instruction, verbatim: "make sure that future deployments have a way of getting sol back this is ridiculous".

## Why SOL was lost

- The devnet payer Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD is also the upgrade authority of the Pool program (BmsNik..., 3.078 SOL) and of the carrier (3jEFrv..., 0.103 SOL). Its keypair file is gone from every recorded host path, and from the build host's and this Mac's home directories. A disk cleanup of a project-offload directory is the likely cause; the lead could not confirm it. Its own 3.708 SOL and those two programs' rent can no longer be moved or closed by anyone.
- The verifier (Gk16sp..., 7.658 SOL) and the registry (9pWwAc..., 1.064 SOL) were finalised. Finalisation is deliberate: the registry accepts a verifier only if its loader-v3 upgrade authority is permanently revoked (programs/aspis-registry/src/processor.rs:208-217). That stops anyone swapping the verifier out from under the soundness argument. Rent on a finalised program is unrecoverable by design.

## Rules for every future deployment (devnet and mainnet)

1. One retained deployment authority per network. The payer, buffer authority, and the upgrade authority of every non-finalised program are keypairs kept in one durable, backed-up location outside every build workspace and project-offload directory. They are listed by public key, mode 0600, in the deployment receipt. No cleanup job may touch that location. A deployment does not start until the key's presence and its public key are checked.
2. Finalise only what the security argument requires. That means the verifier and the registry, which processor.rs:208 makes mandatory, and nothing else. Their rent is reported in advance as permanently locked, and the owner sees that figure before the write. Every other program keeps a retained upgrade authority, so it can be closed and its rent recovered with `solana program close --recipient <payer>`.
3. No stranded buffers. Deploy scripts record each buffer address, and on any failure or abort they close the buffer back to the payer (`solana program close <buffer>`). After every deployment, `solana program show --buffers --buffer-authority <authority>` must come back empty, and that output goes in the receipt.
4. Recoverable state accounts. Fixture and demo accounts (Pool state, proof accounts, probes) are created from retained keys, and a closing instruction or close path is documented for each one, where the program allows it.
5. A rent ledger in every receipt. For each account created, record its lamports, whether they are recoverable or locked, and which key recovers them.
6. Size before finalising. The locked rent scales with ELF size: about 7.95 SOL for the 1.56 MB release verifier. Any later release must report its locked-rent figure as part of the deployment proposal.

These rules govern how deployments are run. They change no proof, protocol or code under crates/ or programs/. Implementing them in scripts/r1_devnet_*.py is a scripts-only change, assigned to a worker.

## Recoverable now (read-only devnet check, 2026-10-29)

- 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue: the July 2026 profile23 devnet program, 8.353 SOL. Its upgrade authority is 8AFmGcC2... (~/.config/solana/id.json, which is present). It can be closed to any recipient. Closing is irreversible and needs owner confirmation.
- Small balances on retained local keys: 0.463 + 0.463 SOL (profile23 proof accounts), 0.397 SOL (.spend-keys/devnet-payer), 0.042 SOL (id.json).
- No open buffers under Xjb7roDV..., 8AFmGcC2..., 9Q3FdNJF... or 6xf6m4fJ....
