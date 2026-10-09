# Authenticated-prefix C1 to canonical coefficients

Working parent: `eb06c838bdeb002508dac2b4af406631f3d67e66`.
Status: source-review draft; focused Lean check pending. No compiler or cache
mutation has been performed for this leaf.

Source: [AuthenticatedC1CanonicalTransfer.lean](experiments/AuthenticatedC1CanonicalTransfer.lean),
SHA256 `37901affa1f18b04c5049e5d527af3f83cd8b3a230d2176c7752e0ca6f2b82ff`.
Nine printed declarations, depth200 and heartbeat250000; no concrete field,
1024-cell enumeration, or new axiom is used in the draft proofs.

## The missing interface being discharged

The selected payment fragments previously required an arbitrary `baseWord`
premise. For the actual early-prefix word this premise is already a V7
theorem, not an authentication or canonicality assumption:

`projectBase_c1Received (prefixWords records root) column index`.

It holds for strict decoded entries and for the zero used at missing or
noncanonical entries. Composing it with `EarlyC1Family.member_is_base` makes
every coefficient of the SAME own-supported family member an embedded M31
value. This does not require `earlyC1=some`, global raw-leaf canonicality,
or shared support with a different tuple.

The leaf constructs canonical natural representatives for all26 lanes and
proves re-embedding returns that member exactly. It also proves uniqueness
of the canonical representatives given a representation; it does not assert
that the family has a unique member or implement its list search.

The executable `StateOnlyTraceFoundation` has16 semantic columns of1024
entries, not26. The constructed first16 lists discharge the literal
`length != 1024 || any(raw >= P)` rejection guard in
`recovered_witness::decode`. Their optional indexed reads and casts are
proved equal to the existing `semanticTable` in row/column order, with no
assumed trace correspondence. The other ten recovered C1 lanes are neither
zeroed nor claimed to be inputs to this decoder.

The canonical guard alone passes even for an arbitrary projected QM31
candidate. The substantive authentication-family bridge is the additional
re-embedding theorem: it rules out discarding non-base coordinates of the
own-supported member. Thus guard success is not advertised as recovery or
payment validity by itself.

## Same-table payment consumer

`prefix_member_canonical_transfer` combines the construction with the green
`SelectedSemanticTransfer.member_transfer_or_copy_collision`. It returns the
guard result, exact re-embedding of all26 lanes, and `TransferFacts` or the
ONE existing sequential copy-collision event.

Its remaining hypotheses are explicit:

- Membership in `EarlyC1Family.family (fixedC1 records root)`; upstream
  residual recovery must be about this same early word.
- The complete selected packed semantic rows vanish on this same table.
  No mask/zero-padding residual is deleted or redefined as acceptance.
- The selected mathematical Poseidon round-pair equations hold.
- Literal `CopyConditions`: all local residuals, both total/inactive helper
  sum conditions, and all four active-row denominator guards, even at
  zero-weight slots. Lambda/chi belong to their original finite domains.

`TransferFacts` covers strict amounts/conservation, input note/owner/nullifier,
input pair field checks and output note commitments. It is NOT a checked
transfer witness. The preliminary guard proved here does not erase the
decoder's later Boolean direction and pair occupancy checks, the payment
compiler, or its final transition equality check.

The first still-missing *source* implication is that actual selected
multiproof execution and its hash-call trace give projection to this early
prefix word outside the shared late-target/collision event; the prior
[authentication reuse map](c1-authentication-reuse-map.md) specifies it.
An early prefix/root alone is not authenticated extractor access. Resource-
bounded recovery of the family member and literal Rust FFT/Gao refinement
also remain distinct from constructing coefficients once that member is
given. Downstream, historical checkpoint/caller authority, unspent-nullifier
context, deployed Poseidon correspondence, and full compiler/settlement
success remain open. No source acceptance, decoder success, honest trace,
or `validWitness` premise is introduced.

## Exact reuse and source conventions

| Source | Reused interface / fact | SHA256 |
| --- | --- | --- |
| V7 `Pool/V7C1SubfieldRecovery.lean` | `projectBase_c1Received`, literal `projectBase` | `49b135edbb05cc5b28b8c8a4bda764664f015a7e63bfbbee75f3ffcc0687a3ce` |
| `EarlyC1Family.lean` | Actual unfiltered family and member-own-support descent | `5131fa466f65931b8c7a8e783e352903b195d12692e56da67bcdfd3918e1ea3a` |
| `AuthenticatedEarlyC1Prefix.lean` | Literal `prefixWords` / `fixedC1` definitions | `a4feb97b426d0251f42bd7315d5fccf8a6c0264c48950fd51bb62d11e993dc9e` |
| `SelectedSemanticTransferV2.lean` | Existing one-collision same-table fragment | `21020c07493be8d6cd247d05d67348a9d6f0bc5830f6f040e475e6f82a97d1d4` |
| `recovered_witness.rs` | Lines44–69: guard and reads; lines71–84: validator/context/transition remain separate | `56760c46ed56ace2756949efabc09f1a2b8880087c1b4dbb7da394a1cc54132f` |

V7 borrowed pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
`state_only_trace.rs` defines `STATE_ONLY_C1_COLUMNS = POSEIDON2_WIDTH`, whose
value is16. These Rust correspondences are source inspection, not a Rust
machine-code refinement theorem.

## Focused-check preflight

The latest retained1067-entry manifest contains the exact
`SelectedSemanticTransferV2` source/output pair. A read-only import census of
the authentication branch found only three absent module pairs:
`AuthenticatedEarlyC1Prefix`, `V7MerklePrefixTargetCongruence`, and
`V7MerkleFirstUnresolvedBinding`; no broad replay is requested. The existing
authentication evidence records the first source/output pair as
`a4feb97b...` / `50d5fd7c...`, Lean4.32.0 and four standard-only audits.
Any required copy-only registration must verify those pairs, all boundary
imports and source pins, preserve the original manifest, and occur with no
compiler active. No untracked nested-circle or stopped-prefix artifact is
an import, an edit target or a publication dependency.

Read-only Tailscale preflight found a native source variant of
`V7MerkleFirstUnresolvedBinding` (`b5f4b0ab...`) that does NOT match borrowed
`26a9`. It must not be substituted. The exact local pairs below still match
the source/output hashes in the retained
[authentication log](experiments/authenticated-early-c1-prefix-v2.log):

| Missing module | Pinned source SHA256 | Retained output SHA256 |
| --- | --- | --- |
| `AuthenticatedEarlyC1Prefix` | `a4feb97b426d0251f42bd7315d5fccf8a6c0264c48950fd51bb62d11e993dc9e` | `50d5fd7cc93aab0f8e28901a3481c5dbe7ca677b6330dacfbd7a3b2e9d0a54dd` |
| `V7MerklePrefixTargetCongruence` | `48392fc0677f2423f4cd43e23a9b8ecc337c66afc1c4dcaf40c910c8967a00ed` | `4d22758124c26c67f0c7372c42b657c711d2dac708961772df033348d9496212` |
| `V7MerkleFirstUnresolvedBinding` | `5cc1eb37267545da85f5c33dd51a24c698d89ccf5d2a9c4d9290f3593618ccea` | `ca895c3697720d96c4481bb545bf35083ba35d2a13b685320765929df77dad88` |

These are transferred Lean4.32.0 artifacts, not newly replayed dependencies.
The base task manifest has830 entries; the later1067-entry per-run manifest
additionally snapshots already-green leaves. Counts must not be mistaken for
a manifest rollback. Copy-only registration is requested, not yet performed.
