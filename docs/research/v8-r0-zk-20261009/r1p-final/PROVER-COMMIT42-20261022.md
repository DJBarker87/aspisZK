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
