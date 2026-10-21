# Prover commitment continuation 9 — 2026-10-21

Branch `codex/cx-prover-commit9-20261021`, base `1be134246`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit9-20261021/`.

## Stage 1: recursive owned balancing

The reference now recurses over ascending rows with a fresh owned accumulator.
It visits exactly the same 1024 rows, uses the existing row transitions, and
retains the shape checks and final dependent-cell assignment. Shipped code
is unchanged. This replaces the continuation-8 loop-context collapse; the
failed lowering is not rerun.

The new extraction succeeds: Charon exit 0, 23.639 s, 670352 KiB peak RSS,
zero swaps, `has_errors=false`; Aeneas exit 0, 0.341 s, 67760 KiB, zero swaps.
Both field additions and subtractions are concrete extracted definitions.
There is no external-function template or unproved arithmetic summary.
The generated Funs is adopted verbatim. Types receives only the documented
explicit discriminant-instance port (`extraction/types-port.diff.txt`).

`ProverCommitBalanceRecursion` proves that each extracted recursion equals
its finite ascending fold for every start row and remaining count whose sum
is 1024. Indexing and arithmetic fail/div are retained. `sequence_ascending`
proves the exact natural row order and bounded nonwrapping successor.
`m31_owned_fold` and `qm31_owned_fold` identify the **whole extracted owned
callers**, including guards and the final write. No concrete 1024-row term
is normalized. Eight printed axioms audits use only standard axioms.

Kani reruns the two row comparisons against the reshaped-reference source:
M31 exit 0, 10.093 s, 531984 KiB; QM31 exit 0, 3.791 s, 488276 KiB; both zero
swaps. They execute the shipped filter/fold transition and compare the
reference step with arbitrary accumulator, value, activity, row and dependent
index. Together with the recursion proof these certify the row/iteration
algebra. They do not themselves certify the shipped Rust outer producer,
its complete coordinate projection, or the endpoint's independently supplied
decoder. No whole-program Kani certificate is claimed.

J8281 Types and J8282 Funs pass. J8283 is an excluded elaboration draft:
the platform-word size bound needed the symbolic `le_numBits` lemma.
J8284 passes the six recursion/order lemmas; J8285 adds the two whole-owned
caller theorems and passes (1.54 s, 2580572 KiB peak RSS, zero swaps).
Exact targets, source SHA, dependency fingerprints, source base revision,
exit, wall, RSS, swap and full axiom/error output are in the Lean JSONL
and verbatim logs. No shared existing source/object is replaced in this stage;
only the new Balance9 namespace is installed. Own new theorem replacements
are snapshotted by the launcher.

Every host gate uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. Rust uses four jobs and the required four-thread linker flag.
The fresh source workspace reuses this worker's pinned compiler caches.
Reservation receipts enforce the 55 GiB aggregate cap. No wallet key is
created or removed.

## Stage 2: exact D112 caller interface

`PrivacyR1HeadlineCallerScope` imports the current D112 `PrivacyR1HeadlineV2`
and checks the exact constructed prover in its signature. `tapeOf_eq_decode`
proves definitionally that this endpoint retains `decode`. The new
`all_none_decode_not_caller` is an unconditional counterexample to automatically
supplying CallerLaw at this constructor: use the allowed all-`none` decoder,
with the same block counts and constructed address/opening data. It applies
the existing symbolic successful-input witness, without enumerating any
stream or tape. `failed_decode_not_caller` is the corresponding general form.

J8286 checks the first two lemmas; J8287 checks the three final lemmas: exit 0,
6.25 s, 4148288 KiB peak RSS, zero swaps, standard axioms only. Source revision
is `7c2b4b9e1` plus the exact attempted additive source SHA in the receipt.

This is an obstruction to a premise deletion **at the present universally
quantified decoder interface**, not a refutation of the shipped prover and
not a claim that the full privacy conclusion is false. A future endpoint can
specialize `decode` to a shipped-execution decoder. That specialization needs
the complete raw pre-balance sample/cursor execution and coordinate transport;
neither the new balancing extraction nor the Kani row tests identify this
independently supplied function. Specializing to `representativeDecoder`
would trivially prove a model CallerLaw, but would not certify shipped code.
No such substitution or replacement premise is adopted.

Accordingly the requested full shipped CallerLaw is not proved. The current
headline theorem, simulator, experiment and error bound are unchanged.

## Stage 3: universal shipped reads and headline

No universal **shipped** read-completeness theorem is established. The
already accepted universal scalar/tower reference support theorem remains
valid; it restricts the callback support of that reference, not the actual
runtime's complete tree/binding/seed/salt/expander log. The new balancing
recursion has no hash callback and therefore cannot fill that execution gap.

`source-frontier.json` checks all four actual aggregate function bodies and
both tool binaries against the earlier failed source-lowering receipts.
They are unchanged. The unsupported shipped outer iterations and the missing
raw-array/cursor/source join are still outside the adopted certificate.
No unchanged aggregate lowering, timed-out whole-loop comparison, or full
regression is repeated. The new success replaces only the owned-balancing
loop failure; it does not convert prior failed shipped lowering into evidence.

D112 has no separate named universal shipped read-coverage binder to delete.
The remaining real/ideal execution joins are retained. Deleting those would
assert a source execution identity not proved here. In particular, proving
all model addresses well-formed cannot establish containment of every actual
runtime callback in those addresses.

The stopping point is the source execution/interface join: a full shipped
CallerLaw must first be stated at a concrete shipped-execution decoder and
joined to its raw sample producer, and source coverage must identify its
actual callback log. The exact D112 counterexample rules out obtaining that
join merely from its current abstract decoder/constructor. This does not
prove that the intended concrete-source refinement is false. The shipped
producer transport, raw pre-balance coordinate equivalence and all-family
runtime coverage remain open. No complete source checklist row or endpoint
premise is discharged. `PrivacyR1HeadlineCallerScope` is the new D112-based
module; it contains the checked scope facts, not a weakened privacy theorem.

## Verbatim before/after of the targeted headline premise

The full before/after source is retained verbatim in `headline-before.lean.txt`
and `headline-after.lean.txt`. Their SHA-256 values agree and
`headline-deletions.diff` is empty: there is no justified deletion.

Before:

```lean
    (R_commit_caller : ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
```

After:

```lean
    (R_commit_caller : ProverCommitCallerInstance.CallerLaw
      (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)))
```

## Frozen ELF check after the final Rust edit

| Artifact | SHA-256 | Bytes | Wall s | Peak RSS KiB |
| --- | --- | ---: | ---: | ---: |
| default | dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34 | 1507400 | 24.363 | 648728 |
| devnet | fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78 | 1507400 | 2.240 | 202800 |
| pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 605704 | 24.211 | 644656 |

All builds and exact `cmp` calls exit 0, zero swaps. `frozen-elf-final-check.json`
and the three build receipts retain the exact features, source pins,
commands, cgroup settings and compiler/linker flags. No executable, ELF,
LLBC, `.olean`, archive or key is committed; caches and keys are retained.

## Final audit

Pending the one frozen combined audit; focused targets above are complete.
