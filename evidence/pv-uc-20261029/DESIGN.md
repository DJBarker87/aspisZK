# D524 minimal user client: preregistered acceptance criteria

Base 683e01efee, branch codex/pv-uc-20261029. No Rust changes precede this commit.

## Boundary and privacy requirement

Private witness input is exactly input nullifier key (32 bytes), salt (32), value (u64 LE), asset (u32 LE); change nullifier key (32), salt (32); recipient owner key (32), salt (32), value (u64 LE): 212 bytes. Digest limbs use eight fixed u32 little-endian limbs. Decode with fixed addresses and schedule, no secret validation branch in the decoder. Canonicality/relation rejection is a separate, explicitly observable obligation. Read exactly one record and EOF from an inherited raw FD, following PV-N7; never put witness bytes in JSON or argv. Existing signing-secret FD remains a separate custody boundary.

Public inputs: action, transaction/account addresses, payment kind, withdrawal amount/destination, deployment domain, lane account bytes, checkpoint bytes, complete leaf sets for all eight lanes, proof-account candidates, output directory. Change value is input value minus recipient value or public withdrawal amount. Input membership and selected half are located locally in the complete public pair-leaf sets. Never fetch per leaf: a selective request reveals the note to a network observer (D159). No networking is implemented. Complete public data is supplied by the caller, independently of the selected secret note.

## Source plan

Preserve the old fixture binary and its modules byte-for-byte as a separate target. New client path has no fixture selector or fixture secret constructor. Reuse statement construction, RealR1_client::prove_for_proof_accounts, publication, TX1/TX2 encoding and JSON output keys except fixture fields. Remove mask_audit unless witness independence is established; never Debug-format a secret-dependent value. Retain recovery material securely; never destroy keys. No fallible operation or early return inside nested loops; put fallible work in small Result helpers; no mutable captures across fallible calls. Extraction refusal is repaired in client source, never in the tool.

## Acceptance gates, once on final client

1. Three release ELFs match the existing pins byte-for-byte. Shared program/library bodies and wire layouts stay frozen.
2. 1,000 fixture-secret pairs against unchanged fixture harness: identical statement, proof input and instruction bytes. Any encoding difference fails; do not adapt the comparator.
3. Own D359(A) paired timing against shipped SHA 30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20: ratio <=1.10 and candidate median <15 seconds. Label throttling; do not repeat pv-c474c combined-client gate.
4. Labelled constant-time decoder check in the exact optimized executable; scope limited to decoder slice, V371 retained.
5. Charon plus verified fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68 ae1-2 translator on new entry path, Types/Funs compiling, standard axioms audit. Record refusals and source fixes; no edited generated semantics.
6. SHA-256 of new client and exact locked/offline Rust 1.94.1 linux_raw client-profile recipe; harness remains building at its existing SDK pin.

All gates offline. No access to ~/.config/solana/aspis-deploy/. No merge, push, repin or deployment. Native N75100–75199 (at most 50 scopes), Lean 75000–75099 (at most 40 attempts), zero Kani; sequential admitted scopes, MemoryHigh=6G, MemoryMax=8G, swap=0. Per-run receipts include command, revision, exit, wall, RSS, swap and axioms. Report incomplete gates honestly; no privacy premise removed merely by native validation or extraction.
