# R1 P3 transcript source inventory

Read-only inventory of the in-tree R1 P3 cost-probe prover and verifier. The
source reviewed is pinned at worktree `HEAD` `5731808b200ee9784b2ed018b9cb9cd7e51be5a2`.
This note records code paths, message order, output types, and constants. It
does not analyze soundness or privacy.

## Scope and source identity

The implementation is in `crates/aspis-r1-cost-probe` and its local-measurement
program wrapper is `programs/r1-cost-probe`. The crate and program identify
themselves as an **UNPROVED R1 COST PROBE** (`crates/.../lib.rs:1`,
`programs/.../src/lib.rs:1`). The private-leaf-salts feature selects the P3
domain/magic (`r1_wire.rs:9-12`, `verifier.rs:40-44`) and the salted prover
entrypoint; the program manifest forwards that feature
(`programs/r1-cost-probe/Cargo.toml:9-19`). This is the P3-feature path in the
cost-probe sources, not a claim that an R1 production protocol is deployed.

The transcript below follows `host_semantic::build_with_helper_mode` on the
prover side and `r1_semantic::verify_observed` / `verifier::Prepared::new` on
the verifier side. `semantic_wire.rs` is a separate semantic path with the
legacy R0 domain and a different row-25 payload shape; it is not the R1 P3
path described here. The R1 path reuses the R0 `Public` terminal relation and
the R0 `Challenges` type alias, but its rows and transcript state transitions
are explicitly handled by `r1_wire.rs` (`r1_semantic.rs:103-113`,
`r1_wire.rs:341`).

## Semantic commitment and challenge schedule

`row` below means the explicit R1 transcript row passed to the sampler. Row
records have a one-byte tag and four-byte little-endian payload length before
their data (`r1_wire.rs:38-49, 76-85`). The C1 Merkle root precedes the records
as a 32-byte value (`r1_wire.rs:265-292`).

| Order | Committed/input message and transcript action | Output / source |
|---|---|---|
| Before row 0 | C1 commitment root, 32 bytes. C1 commits lanes `0..=25` and `28`; the base lanes `0..=25` are M31 columns and lane 28 is the extension-valued `D` column. Prover constructs the 27-column argument and commits it before initializing the semantic transcript (`host_semantic.rs:72-83`). | `Backend::c1` maps input columns to message indices 0..25 and 28 (`prover.rs:9-14`); commitment lanes and leaf encoding are `host_commitment.rs:159-210`. |
| 0 | Empty record; sample `lambda`. | `QM31`, via `semantic` → `qm31_sample` (`host_semantic.rs:84-92`; `r1_wire.rs:243-248`; `sampler.rs:8-24`). |
| 1 | Empty record; sample `chi`. | `QM31`; same function. Prover derives H1 from the trace helper using `(lambda, chi)` and applies H1 padding before C2 (`host_semantic.rs:90-102`). |
| C2, before row 2 | C2 commitment root is computed over H1 and G, two 1024-entry `QM31` columns. They occupy lanes 26 and 27 (`host_semantic.rs:98-103, 109-114`; `prover.rs:15-19`). | `CommitmentTime::C2` selects lanes `[26,27]` (`host_commitment.rs:159-165`). The root bytes are the row-2 payload. |
| 2 | C2 root payload; sample `theta`. | `QM31`, via `qm31_sample` (`host_semantic.rs:102-104`; `r1_wire.rs:41-44`). |
| 3–12 | Ten empty records; sample `zc[0]` through `zc[9]` in increasing row order. | Each is `QM31` (`host_semantic.rs:104-107`; `r1_wire.rs:351-354`). |
| 13 | Empty record; sample `mu`. | `QM31` (`host_semantic.rs:108`; `r1_wire.rs:355-356`). |
| 14 | 32-byte `WideExact::from_qm31(mask_sum)` payload; sample `eta`. `mask_sum` is computed from the selected mask value over all 1024 rows plus the two 28-coefficient D tails (`host_semantic.rs:115-142`). | `eta : QM31`; row 14 uses tag 3 and a 32-byte payload (`r1_wire.rs:43-46`). |
| 15–24 | Ten semantic-round records, rows in increasing round order. Each message is 28 `WideExact`-encoded polynomial coefficients (896 payload bytes); the prover obtains the polynomial from 28 interpolation samples. | For each row `15+i`, verifier checks `state_only_boundary_sum(poly) = running`, samples `alpha[i] : QM31` from that same framed record, then evaluates the polynomial at `alpha[i]` (`host_sumcheck.rs:46-78`; `r1_semantic.rs:83-100`). The row tag is 2 (`r1_wire.rs:44-46`). |
| 25 | `beforeZ0`: 87 point-claim values (three points × 29 lanes) followed by 29 extra values, all encoded as `WideExact`; payload length 3712 bytes. | Samples `z0 : SecureCirclePoint` with the first-circle mapping (`host_semantic.rs:167-178`; `r1_wire.rs:45-46, 228-241`; `sampler.rs:94-100`). |
| 26 | `beforeZ1`: 29 endpoint evaluations, each encoded as `WideExact`; payload length 928 bytes. | Samples `z1 : SecureCirclePoint` with the second-circle mapping (`host_semantic.rs:179-187`; `r1_wire.rs:45-46, 228-241`; `sampler.rs:94-100`). The verifier rejects equal circle points (`r1_semantic.rs:127-130, 152-154`). |

The semantic transcript starts as `hash([DOMAIN, [0], public_len_u32_le,
public_bytes, c1_root])`; each row checks sequential order, absorbs
`[old_state, [0, 0xa0+row], framed_record]`, derives the challenge block from
`[absorbed, [1]]`, and advances state using `[absorbed, [2]]`
(`r1_wire.rs:163-201`). Semantic challenges call `qm31_sample`, which divides
the 256-bit block into four base-P limbs and returns `QM31` (`sampler.rs:8-24`).
Circle rows use that sampler and map the result through
`secure_ood_circle_point_from_parameter`, with fixed row-specific fallback
(`sampler.rs:94-100`).

The prefix is exactly the C1 root plus rows 0 through 26; its semantic rows
have the above shapes (`r1_wire.rs:265-292`). `SEMANTIC_BYTES` is
`12903 + 29*32 = 13831` bytes (`verifier.rs:8`, including the root and all 27
framed rows).

## Opening and query schedule

After row 26, both parties initialize the opening `Transcript` from the
semantic state and variant tag. Its P3 domain is
`UNPROVED:R1:PRIVATE-SALTED:P3` (`transcript.rs:5-12`). Row payloads in this
opening transcript are length-prefixed as `u32` on absorb; scalar challenges
consume one block and advance (`transcript.rs:14-33`). Before commitment
encoding, each message is transformed by `Variant::coefficients`; `S1` and
`S2` use the D18 five-digit permutation `TAU = [3,4,2,0,1]`, while `D` uses
the retained R0/D13 row map (`transport.rs:1-22`; `host_commitment.rs:184-191`).

| Order | Message / challenge | Output / source |
|---|---|---|
| 27 | `y1`: 29 evaluations of encoded messages at `z1`, encoded as 29 `WideExact` values; sample `gamma`. | `gamma : WideExact` (E), sampled with `gamma_sample` (nonzero mapping) (`prover.rs:191-196`; `transcript.rs:23-26`; `sampler.rs:84-92`). Verifier consumes identical bytes (`verifier.rs:87-90`). |
| 28 | `inactive : WideExact`; sample `kappa`. | `kappa : WideExact` (E), using `ordinary_sample` (`prover.rs:197-200`; `verifier.rs:89-90`; `transcript.rs:23-26`; `sampler.rs:73-78`). |
| 29 | Seven `WideExact` coefficients of first round polynomial `c0`; sample `alpha0`. | `alpha0 : WideExact` (E), ordinary mapping; fold q and weights (`prover.rs:201-202`; verifier `Prepared::new` at `verifier.rs:91`). |
| 30, when `folds()==2` | Folded-word Merkle root (32 bytes) concatenated with seven `WideExact` coefficients of second round polynomial `c1`; sample `alpha1`. | `alpha1 : WideExact` (E), ordinary mapping; fold again (`prover.rs:207-227`; `verifier.rs:92-95`). `Variant::S1` uses one fold; `S2` and `D` use two (`transport.rs:2-9`). |
| 30 for one fold, 31 for two | Final message, encoded as `WideExact` values. Absorb and derive 22 query indices from eight block/advance pairs. | `queries : [u32;22]` (`prover.rs:228-242`; verifier `Prepared::new` `verifier.rs:96-98`; transcript query derivation `transcript.rs:35-45`). Final-message length is `1024 >> (2*folds)` (`transport.rs:8-9`). |
| 31 for one fold, 32 for two | Empty payload; sample `rho` after query derivation. | `rho : QM31`, using `scalar_k` / `qm31_sample` (`prover.rs:228-229`; verifier `verifier.rs:96-99`; `transcript.rs:31-33`). |

The eight query block/advance pairs feed the shared
`aspis_core::r0_transcript::queries_from_pairs` helper, returning exactly 22
indices (`transcript.rs:35-45`). The query row and final-message absorb remain
part of the R1 opening schedule.

For two-fold variants, the prover commits the intermediate folded word under
tag `0x72` before sampling `alpha1`, and query openings include the folded
word values and path (`prover.rs:207-226, 251-256`; verifier checks that
folded commitment at `verifier.rs:253-263`). The verifier's `Prepared` record
stores roots, `gamma`, `kappa`, both fold challenges, `rho`, query indices,
ten semantic challenges, and two circle points (`verifier.rs:81-83`).

The verifier replays the semantic prefix first, then replays the opening
schedule in `Prepared::new`; query checks consume both C1 and C2 Merkle paths,
and the optional folded path (`verifier.rs:342-349, 360-365, 245-274`). This
describes code-level order only.

## Separation from the legacy R0 model

The P3 wire path here is `r1_wire.rs` plus `r1_semantic.rs`, not
`semantic_wire.rs` / `semantic.rs`. R1 row 25 includes both 87 point claims
and 29 extras, whereas the separate legacy semantic wire's row 25 carries
only `CLAIMS` values (`semantic_wire.rs:38-48`, versus `r1_wire.rs:38-49`).
The R1 prefix binds the C1 root at initialization and places the C2 root in
row 2 after `lambda` and `chi` (`host_semantic.rs:81-103`). R0 challenge
struct/relation reuse is visible in `r1_wire.rs:341` and
`r1_semantic.rs:103-113`; that reuse does not make the transcript schedules
identical.

## Source hashes

SHA-256 values are for the working-tree source files inspected at the pinned
HEAD above.

| Source | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/host_semantic.rs` | `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf` |
| `crates/aspis-r1-cost-probe/src/host_commitment.rs` | `551c4f8a0df50e0b53ab7e79d4e71b8c6afe417043c55caa1c377da3388f890c` |
| `crates/aspis-r1-cost-probe/src/host_sumcheck.rs` | `f983229f9ea0c54954301c2dbb8255df6581a4def4f55d95b012c2bf47e9d1f1` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/prover.rs` | `a7e20e5eb2fb706f2bdb51371466d4ee02c6fcabc67a427495a3b9276d9495fd` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/sampler.rs` | `be426dfc4049682ef2d90940ee42bf9cffbec2db1d2d9b965e9c14e491948b8c` |
| `crates/aspis-r1-cost-probe/src/transport.rs` | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` |
| `crates/aspis-r1-cost-probe/src/lib.rs` | `f68b59010023a1adc9aea104068bbfbd715a9e8d7daf1cc033e3e84406ba1402` |
| `crates/aspis-r1-cost-probe/Cargo.toml` | `5fafcd2572896d4ba35cb01304aa6ccde1d0b634804fedf22c3f74133cedf093` |
| `programs/r1-cost-probe/src/lib.rs` | `66fcf176252443d0b3956797c8e854815cc8b6f8871a7cb5e246bea58dbf67fa` |
| `programs/r1-cost-probe/Cargo.toml` | `1208d93c95f3e4e769fd1ba48f71bbb031c4ddd33793f09f5cc6405fe9da71f1` |

No builds, prover runs, verifier runs, or source edits were performed for this
inventory.
