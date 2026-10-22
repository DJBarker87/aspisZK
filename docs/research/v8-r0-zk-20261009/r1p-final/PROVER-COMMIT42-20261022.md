# Prover commitment continuation 42

Work in progress. Target not yet established.

The task base is f57f0546d8af9a4355a3df1f8eaf91dc7a4e33c4 (the fresh
worktree supplied to this continuation). No shipped sources changed.

## Raw private domains

`ProverCommitRawFresh42` closes the unverified part-41 domain-separation
draft: all three raw seed families differ from both public bindings, and
outside `PrivateMemo40.guessed` they avoid the retained old history plus
both binding reads. The statement digest address remains a separate
obligation; no private-derived read bound is replaced by this result.

J9442 is a rejected draft (simplifier did not reduce `if True`);
J9444 compiles the corrected module: exit 0, wall 2.15 s, peak RSS
4,163,112 KiB, zero swaps. All three printed axioms lists are subsets of
[propext, Classical.choice, Quot.sound]. Exact source bytes, dependency
fingerprints, source revision and commands are in
`../../100bit-spend-path-20261013/evidence/prover-commit42-20261022/lean/`.

J9400 was refused because its receipt already exists for another module;
no compiler ran and its existing evidence is not attributed to this work.
A read-only range inventory identified available numbers within J9400–J9799.

## Selected generated owner

The unchanged generated Types/Funs from part 41 are now installed and
compiled independently (J9443/J9445), exit 0, standard generated definitions.
The semantic bridge is in progress; compilation alone is no refinement claim.

## Generated 64-byte owner bridge and reservation (local closure)

`ProverCommitOwnerZero42.zero_from` proves the extracted recursive byte test
for every full array by symbolic suffix-length induction. `OwnerBytes42`
connects the U8 arrays to the ROM's UInt8 functions, including exact zero
and nonzero equivalence. `OwnerRun42.run_exact` and `generate_exact` prove
the extracted selected owner against the byte-blind schedule for arbitrary
64-byte tapes, including OS errors and retained cursor/history/ledger.
`OwnerModel42.generate_model` then projects this execution to
`ProverCommitPublicNonce40.generate`. `OwnerLedger42.prepared_model` and
`continuation` compose the exact selected owner with part-36 reservation
and any subsequent continuation, retaining its full state. These are local
control/model theorems; they do not certify the native entropy callback's
entire caller or mask/publication continuation.

The generated Types module's global `instDiscriminantErrorIsize` conflicted
with the prover extraction in J9449. The fix replaces only that attribute
with `errorDiscriminant42`, preserving Os=0 and RepeatedZero=1. The Types
source and object were snapshotted under the task host workspace before
overwrite; Funs and zero-test dependencies were rebuilt. Thus this is a
shared object replacement, not reuse of a stale dependent.

Accepted final targets: Types J9450 (1.40 s, 2,562,376 KiB), Funs J9451
(1.33 s, 2,559,720 KiB), zero J9452 (2.15 s, 3,727,520 KiB), bytes J9454
(2.15 s, 4,151,560 KiB), run J9458 (2.05 s, 4,164,496 KiB), model J9459
(1.91 s, 4,163,452 KiB), ledger J9468 (1.87 s, 4,163,964 KiB).
All exit 0, zero swaps. All printed theorem axioms are subsets of
[propext, Classical.choice, Quot.sound]. Draft failures and all section-6
fields are retained in the attempt JSON and raw receipts. No native bounded
check was rerun, and no new OS RNG, nonce or ledger assumption was added.

## Concrete conditional private-read carrier and run transport

`ProverCommitGlobal42` defines the two public positions in the actual
`gAddr`/`attVec` order. `normalized_attVec` and `normalized_rest` prove the
exact projection to the local binding substitution. `conditional_law`
instantiates part 41 on `aA` (the finite-ROM encoding of `gAddr`) with an
arbitrary frozen context that covers the statement digest. It retains an
unnormalized context indicator, including empty fibers.

`ProverCommitPrivateBounds42` uses a carrier containing **two** independent
nonzero private seeds and the answer vector; the public nonce and both
binding answers are fixed parameters. `src_private` shows that a private
commitment position never uses the public nonce or a binding answer as its
designated freshness field. `seed_field`/`answer_field` establish the actual
grammar fields on this carrier. `private_pair` preserves the old designated
field argument; `fixed_mass` gives ≤2^-255 against any fixed frozen address,
and `frozen_mass` gives q/2^255 for q retained addresses, with repetitions.
This covers mask expansion, D-seed, source expansion, salts, leaves and
Merkle nodes. No private-derived read is replaced by raw-seed counting.

`ProverCommitPrivatePairs42.pair_all`/`pair_mass` preserve the private/private
pair bound, using the existing structural dependency/separation theorem.
`ContextBounds42.context_frozen_mass` integrates the bound against the
context indicator, retaining its probability factor. Its `normalized_local`
and `global_private_address` identify the **actual** `gAddr`/`attVec`
coordinates with this bounded carrier.

`ProverCommitGlobalRun42.run_eq` proves the honest `runC` equation (rather
than assuming a run callback), under public memo coherence and the private
frozen-hit/pair complements. `continuation` transports any subsequent
observation of that vector with an arbitrary retained state. This is a
pointwise local continuation theorem; the complete adaptive eight-attempt
source/experiment composition, charged observer queries, and actual native
publication are not inferred from it.

Accepted final targets: Global J9464 (1.98 s, 4,178,832 KiB), PrivateBounds
J9472 (2.18 s, 4,176,908 KiB), PrivatePairs J9480 (2.21 s, 4,172,328 KiB),
ContextBounds J9478 (1.91 s, 4,166,340 KiB), GlobalRun J9482 (2.01 s,
4,161,368 KiB). All exit 0, zero swaps, printed axioms only in
[propext, Classical.choice, Quot.sound]. J9474 hit the ordinary heartbeat
limit during underspecified elaboration; the replacement supplies explicit
grammar arguments and a symbolic update equality, with no limit increase.
No existing inherited module was changed for these new proof modules.

## Charged adaptive reads and selected retry control

`ProverCommitNormalCarrier42` embeds fixed nonce/binding values into the
existing coupling carrier, leaving the old public coordinates unused. Its
commutation lemmas show that private seed/rest lenses leave these fixed
public values intact. `ProverCommitCharged42.hit_private` instantiates the
existing charging and adaptive observer argument on this normalized carrier.
It uses the actual `qry_tame`, `charged_tame` and `verLog_rest` proofs; it does
not assume the observer's query remains unchanged. `CarrierJoin42` proves
that this carrier's `uVec` is precisely the `gAddr` normalization above, that
the public nonce is fixed, that both private seeds are retained, and that
charged private observer hits have mass ≤2^-255. Public bindings are excluded
from the freshness theorem.

`ProverCommitOwnerSuccess42.source_success` retains the entire selected
owner's successful output, including the exact public nonce, both private
blocks and state. `RetryOwner42.entropy_model` installs the extracted selected
64-byte owner as the entropy callback of `ProverCommitRetry34.realAttempt`;
`eight_model` transports it through all eight attempts, before the actual
serializer guard, retaining every state update. This is a local selected
callback/control theorem with an unrestricted subsequent continuation; it
does not assert that the entire downstream native prover has been refined.
Reservation remains in the successful continuation, so it is not moved before
the native public-byte guard.

Accepted focused targets: RetryOwner J9483 (1.95 s, 4,160,608 KiB),
OwnerSuccess J9485 (2.26 s, 4,152,768 KiB), NormalCarrier J9488 (8.68 s,
4,117,772 KiB), Charged J9487 (4.75 s, 4,133,152 KiB), CarrierJoin J9492
(1.99 s, 4,164,724 KiB). All exit 0, zero swaps, standard axioms only.
J9487 initially stopped in dependency preflight before a pin or compiler
receipt existed; its source snapshot is retained as `preflight-9487-*`.
After NormalCarrier compiled, J9487 was used for exactly one real compile.
No existing receipt or source/dependency compilation was rerun unchanged.
