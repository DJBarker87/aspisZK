# Confirmed isolated V8 COMPLETE devnet demonstration

The genuine positive private transfer **confirmed and finalized** at slot
495678563, using **1,083,081 CU of the declared 1,200,000**.
The 1,000-unit input produced recipient/change notes of **600 and 400**.
All exact settlement assertions passed. Malformed-proof and replay simulations
rejected with settlement accounts unchanged.

[Confirmed atomic transaction](https://explorer.solana.com/tx/2nmxBqds4N63HUZJGkrewaQp1V1ougZgnWnarxnia8JVcYjWGTCKHuSkMc63AGNpt4FigwrFn2CePutB4PKMnHFD?cluster=devnet)  
Signature: `2nmxBqds4N63HUZJGkrewaQp1V1ougZgnWnarxnia8JVcYjWGTCKHuSkMc63AGNpt4FigwrFn2CePutB4PKMnHFD`

This establishes live engineering functionality only. It is experimental devnet
deployment, not production activation or a statement that soundness is complete.
Global recovery, payment/source refinement, Fiat–Shamir and full-view ZK remain
under formalisation. No claim was changed or formalisation worktree modified.

## Runtime and provenance

Source base: `bc945367d6b0d9a5b4cb2dc5a9ecad8ddcfb33ee`, the appropriate committed
research checkpoint at isolation. Own branch:
`research/v8-isolated-devnet-smoke-20260909`; own worktree:
`/Users/dominic/ZK/.worktrees/ZK-v8-isolated-devnet-smoke-20260909`.
The receipt setup repair was committed as
`c2ec813417f388d2baf6c5209eb227e843a7a019`; rent recovery followed in `bc243d2f`.
The final scoped evidence commit is reported by the execution agent and git log.
Main and the formalisation branch were not reset, modified, merged or pushed.

Devnet genesis: `EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG`.
Live gate recorded runtime `4.3.0-beta.3`, feature set `2409014235`;
Helius response contexts also identify `4.3.0-alpha.2`. These load-balanced
versions are preserved, rather than pretending one validator binary was pinned.
The TxV1 feature `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` was active from
slot 492480000. The confirmed settlement is transaction **version 1**, 845 wire
bytes, explicit 1,200,000 CU, 256 KiB heap and 8 MiB loaded-account limit.
Fee: **15,000 lamports** (5,000 signature fee plus 10,000 declared priority fee).
Exact signed simulation and confirmed execution both consumed **1,083,081 CU**.
Verifier CPI logs report 1,033,784 CU; that is not the full transaction metric.

The selected archived optimized COMPLETE ELF was authenticated at SHA256
`3d07a23833bac533f791b7ce2d619f4cd40aff6e1b5314c3b43be596b38c15a3`
(1,027,608 bytes), against the frozen NUC artifact and terminal-query evidence.
The recorded ledger had 122 complete cases and 15 clean axioms audits; these
were existing-evidence checks, not a new full formal replay.

Fresh identities required capability rebinding and adding dispatch to the
existing proof initialization/upload/seal/close handlers. The Pool additionally
uses the default-off checkpoint receipt setup extension documented in
[checkpoint-fix-review.md](checkpoint-fix-review.md). The selected COMPLETE
verification kernel and grammar checks were preserved. **The rebuilt verifier
is not byte-identical to the archived ELF.** Changed input/source hashes are
in `build-inputs.json`, `prover-input-change.json`, `checkpoint-final-artifacts.json`
and the scoped build adapters. Exact finalized executable payloads were compared
to the retained local ELF bytes.

| Program | Fresh public program ID | ELF bytes | SHA256 |
| --- | --- | ---: | --- |
| verifier | [9Q2m6188rFLiWdYnttKYhMjbfarQXdq9D4HzS23eTkqc](https://explorer.solana.com/address/9Q2m6188rFLiWdYnttKYhMjbfarQXdq9D4HzS23eTkqc?cluster=devnet) | 941,672 | `a4dd7d5ab699cd32fececb5f8a382df8e2f2f9bf6f6810b865d5a9084606eaab` |
| pool | [CWc8x6vhwX5UUUwNE6ys5vjT5vPUYahHu1JmEG8DtJMr](https://explorer.solana.com/address/CWc8x6vhwX5UUUwNE6ys5vjT5vPUYahHu1JmEG8DtJMr?cluster=devnet) | 537,728 | `e07dc1e7445a0256c6da7a9833e7946cc0225e9076db1dd350f914dac500d108` |
| registry | [5t5jGysv18VHEHrjhoTKeV3n1Jw7cfDqmMvadxU2UiQV](https://explorer.solana.com/address/5t5jGysv18VHEHrjhoTKeV3n1Jw7cfDqmMvadxU2UiQV?cluster=devnet) | 193,416 | `76f4c382de8c638084cd3c15d50398224e5ad377eeebfbc15d6f35a61f0f045d` |

The Registry program was created by this isolated experiment and reused for
its new master/release accounts. The new Pool keeps payer upgrade/close
authority. Only after real live setup and proof-account lifecycle gates passed
was the new verifier made immutable, as required by the existing Registry V2.
That verifier's rent is irrecoverable. Pool authority and all local keys remain
retained. This authority policy differs from the benchmark's immutable Pool fixture.

Host Rust 1.94.1; SBF platform tools v1.54 / Rust 1.89 development;
Solana CLI 2.3.0; Python 3.12; solders 0.27.1. Builds and optimized proof generation
used the authorized `dombarker` NUC, cached dependencies and cgroups with
MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0. No paid job was used.
Host tools ELF SHA256:
`d36fe97b64ebbcd04f323f9f53fa08eb27a5db5fe09574eb686ace8aae007f7b`.
Prover ELF SHA256:
`6be1b84dc277b099fa3fb45bd688a29958de6ade43f1a254c15a98f4fb80b311`.

## Authoritative setup and proof

All state was established through real loader/System/SPL/Pool/Registry
instructions. The benchmark's direct injection of program, ProgramData,
funding, master, lanes, checkpoint, history, token and sealed-proof accounts
was replaced by those live instructions. Thirteen fixed 1,000-unit synthetic
deposits filled all eight lanes. Seven deposit transactions preserve the fixed
order, with two deposits per transaction except the last; maximum confirmed
batch cost was 1,114,746 CU. Eight strict AS8V lane validations followed.
AS8K checkpoint finalization confirmed at **225,796 CU**, declared 1.2M:
[checkpoint transaction](https://explorer.solana.com/tx/56QwQPSZzoGSZVkzyMo1Uk77akRFujWv3xKfSA8NQB56B2gazdSzKEBvGyGKY8RjgF73nyNyE8UhZXup8SN4ZiAr?cluster=devnet).
All eight canonical lane trees and the checkpoint matched the host planner.
No COMPLETE verification was split across transactions.

The finalized authoritative proof context was fetched at slot **495677200**,
after Registry schedule/activate/freeze and before proof generation.
Registry generation 3 is frozen, release entry active, executable/profile/release
hashes correct, proof/verifier identities fixed. The genuine compiler matched
the expected live transition. Statement SHA256:
`32a688701ec9a09ed61bd3fd9de19531edeae2f9f8f6a7f7cce70407e2f43def`.

The genuine prover uses QM31, q22, current domain, canonical fields, maximum body
40,282 bytes, carried image gate, shifted ordinary rows and shifted query batch.
It used exactly the normal synthetic seed **1**, zero stress/search attempts,
and zero grinding security credit. Positive note values are 1,000 → 600 + 400,
with output owner keys derived from retained fixed synthetic spending secrets.

Proof generation: **3.198629727 s** excluding compiler/encoder setup
(**1.401321057 s**); complete process wall **4.64 s**, peak RSS **202,672 KiB**,
zero swaps, exit 0. Host verification from public bytes and bounded mutation/
truncation checks passed. `evidence/live-prover.log` records the phases.

| Component | Bytes |
| --- | ---: |
| Genuine proof body | 39,502 |
| Candidate afterstate prefix | 688 |
| Uploaded payload | 40,190 |
| Sealed account header | 40 |
| Total proof account data | 40,230 |
| Atomic settlement wire transaction | 845 |

Proof body SHA256: `2102c8649db38cc04388dd2624aaa58134804e375287cd5fc2d85e26ecb98750`.
The genuine lifecycle used one create/init transaction, fifteen writes of at
most 2,800 payload bytes, and one seal: **17 transactions**, separately from
settlement. It cost **345,000 lamports** in transaction fees and retains
**205,018,640 lamports** of refundable proof-account rent. No proof key was burned.

## Exact settlement and controls

Before snapshot slot 495678520; after slot 495678586.
Output lane 3 sequence **1 → 2**, with canonical root bytes:

* Before: `2d576b23b0ea731d2f0d105962d2bb50f51be95a3230ad2367d69257c8be6c5a`
* After: `886282460b1ee85ff7518005f89d69503470ed628255915623182270de3fe454`

The complete lane image, including frontier, exactly equals the canonical
expected image. The existing history page receives the exact sequence-2 root
and equals the expected full page. The nullifier marker changes from absent
to the exact expected Pool-owned payload, retaining anchor/profile/release
bindings. Returned Pool statement/result bytes exactly match the compiler's
expected result. Lane and history rent balances are unchanged.

The other seven lanes, master, checkpoint, Registry and release entry are
byte-for-byte unchanged. Mint supply remains 13,000, source balance 0 and
vault balance 13,000; this private note transfer does not withdraw tokens.
Payer decreases exactly **1,721,880 lamports** = 15,000 fee + 1,706,880 new
nullifier-marker rent. The proof remains sealed/read-only and byte-identical;
consumption is enforced by the nullifier marker.

Malformed control: same proof identity, genuine candidate/body length, first
body M31 limb replaced by modulus 2,147,483,647. The real verifier was invoked
and rejected with Custom 3 at 75,197 CU. Settlement snapshots are identical.
The malformed account was legitimately closed, its 205,018,640-lamport rent
refunded, then recreated for the unchanged genuine proof.

Replay control: fresh blockhash, same genuine terminal request; rejected with
Pool `NullifierAlreadyConsumed` (`0x41532026`) at 24,346 CU. Settlement snapshots
are identical. Both negative transactions were **simulated, not submitted**;
RPC simulation balance checks also proved settlement balances unchanged.
The separate lifecycle preflight rejected sealed writes and confirmed close/refund.

Full account-image hashes, balances, slots, exact assertion flags and individual
confirmed receipts are in [live-summary.json](evidence/live-checkpoint-fix/live-summary.json)
and [settlement-assertions.json](evidence/live-checkpoint-fix/settlement-assertions.json).

| Account | Public ID |
| --- | --- |
| Payer | `FrxmxTHqFqqqRj1MQB4FKNx8Bg4eCiHwqVNDbgwPuBu4` |
| Master | `8kpWQhoJnxJVQ6YDPAYtjiNFF9Qaokbdk9KcMB6XHfvH` |
| Registry account | `HtNhMMMuRjYcxB6Exu22GJ6H2nvuRefoqbrEsB9o9Yig` |
| Registry release entry | `5GjVpDuZhC6WcoNeqgzta4QWDHVmBjHnNeLnWxeFPAMs` |
| Mint | `6ACkKz7kiva7K6PnDyAMQ7WFS4Rtxn34deEuKDKDaTNY` |
| Vault | `A7QsLq3Zs4DPRDDjgDw39MRXimtqWZ5u5JqapQwDdb6W` |
| Checkpoint | `3euoTJj1tGUn9URWbgFJcRVNdJEtBBBk1p5p8vXQaDV9` |
| Output lane 3 | `8sEFFhN6Aw6StEGcz1htvwVJgH5sFFXeEBgd5PM6dxef` |
| Current history page | `3JxCQKE7YqELkDLcRxt6FcFwm6CwFb2aLyGE4u98LSce` |
| Nullifier marker | `AB95BE1qZDywiRHDB3Xc4vWNvEnk2nEupFRKh2R7AK9L` |
| Sealed proof | `5g3WAYhsWUsuAFntb278rsTRecvBY36HYsKaigvR9bF1` |

## Funding and transaction accounting

The user authorized up to 25 faucet-funded devnet SOL. Original payer funding
was 10 SOL. With explicit recovery authorization, dedicated Colosseum devnet
regression/hedge wallets transferred another **8 SOL** in
[the funding transaction](https://explorer.solana.com/tx/4hnKG3nVMZdttprgSEZqAmEhGajvaNPpPRL9BuaCmWtn6FDPwrLudBDNActQb7L8JYEV9snUoE8jKno9Tb12Ukn5?cluster=devnet).
They retained 0.998280480 and 1 SOL. Total external funding: **18 SOL**, within
budget. No Rat, Solvasion or Colosseum game/program accounts were closed.
Two superseded empty task token accounts returned 2,976,880 lamports gross;
see [rent-recovery.md](rent-recovery.md). Final payer balance at slot 495679024:
**0.885174871 SOL**, with all keys retained locally.

The original immutable programs retain 8.435741320 SOL, irrecoverable through
the loader after authority removal. New Pool/verifier program rent totals
7.518775920 SOL; the new Pool's authority remains available. Existing evidence
explains the initial premature finalization and the corrected deployment policy.

These counts cover this resumed run's harness receipts; previous attempts
remain separately preserved under `evidence/live/` and `evidence/live-minimal/`.

| Category | Confirmed tx | Fees (lamports) | Total wire bytes |
| --- | ---: | ---: | ---: |
| atomic settlement | 1 | 15,000 | 845 |
| pool registry setup | 23 | 415,000 | 12,431 |
| funding | 1 | 25,000 | 418 |
| genuine proof lifecycle | 17 | 345,000 | 45,993 |
| lifecycle preflight | 4 | 85,000 | 1,464 |
| malformed control lifecycle | 18 | 365,000 | 46,286 |
| program upload | 414 | 6,220,000 | 1,598,784 |
| prior rent recovery | 1 | 20,000 | 366 |

The two native CLI deployment transactions are additional to the table:
Pool and verifier each used 2,970 CU and paid 10,003 lamports (legacy
deployment transactions, not the measured TxV1 settlement);
loader buffer balances become program rent and are not double-counted as a
second retained cost. Their signatures and raw fee receipts are retained in
program authentication evidence. Every submitted harness receipt is resolved
as confirmed or explicitly expired; no unresolved submitted phase remains.

## Differences from the frozen benchmark and reproducibility

Frozen current-history transfers measured about 1,008,055–1,009,367 CU, with
1,047,041 the recorded maximum across benchmark cases. This live transaction
measured 1,083,081 CU: it uses fresh identities, a live-bound fixed transcript,
rebuilt images and the live runtime. Those are not identical paired inputs,
so this report does not attribute the whole difference to runtime overhead.
Both are below 1.1M. The earlier devnet >1.4M failure was **checkpoint creation**,
not atomic transfer verification. Its replacement adds authenticated lane
receipts during setup; all original root checks remain bound to the exact
consumed bytes. The local checkpoint diagnostic was 237,796 CU versus live
225,796 with new identities. It is explicitly separate from settlement cost.

The RPC initially rate-limited concurrent uploads (429). The scoped harness
now shares a 0.35-second cross-process RPC pacing lock, two upload workers and
bounded retries. It retains existing buffers, verifies exact uploaded bytes,
resolves expiry before replacement signing and preserves every failure.
No proof seed, verification rule or compute limit was changed to recover transport.

See [README.md](README.md) for build/input provenance and ordered commands.
`run_live_prover_nuc.sh` records the actual bounded prover invocation.
`devnet.py`, `upload_program.py`, `deploy.py`, `authenticate_programs.py`,
`lifecycle_preflight.py`, `certify_verifier.py`, `run_transfer.py` and
`summarize_live.py` reproduce the scoped workflow and public evidence extraction.
Successful phase receipts are resumable; do not regenerate existing keys or
rerun an already consumed positive fixture as if it were a new transfer.
All private keypairs/context/proofs are retained outside git with private
permissions. No keys, API credentials or secret-bearing logs are committed.
