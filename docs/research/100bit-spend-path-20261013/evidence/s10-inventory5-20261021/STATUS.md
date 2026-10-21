# S10 pass 5

## Stage 1: complete indirect dispatch accounting

All thirteen remaining owned Pool callback instructions now have corroborated
compiler target-flow evidence for `processor::solana_sha256`. The new narrow
aggregate rule follows offset 288 of the noalias/readonly `context` formal of
`apply_prepared_settlement_plan_v1`. Its sole final caller stores the constant
callback into a private alloca immediately before the call, in the same block;
the target aggregate is not passed as any other call argument. All final
caller multisets and function-address escape checks remain mandatory. Multiple
LLVM calls in a function are never paired to ELF instructions by textual order:
every candidate must resolve to the same target set.

The result is 21 compiler-resolved sites (15 SHA callbacks and six null observer
operands), including pass 4's eight. This is compiler calling-convention/SSA
provenance under the frozen compiler boundary, not a Lean source refinement.
The separate independent replay checks every classification and rejects lost
callers, escaping addresses, unknown operands, and changed field offsets,
constants, store chronology, readonly/noalias attributes and alloca provenance.

The other 131 sites have individual instruction-address/register/caller entries
in `indirect-boundaries.json`: 130 formatting/vtable calls and one boxed
bincode-error drop. Two explicit operational specifications cover exact ABI,
live receiver/vtable provenance, mutable state, callback/write order, ordinary
errors, panic/abort, allocator behavior and confinement from spend-oracle/account
state. These are proposed trusted library boundaries, not proved target sets,
owner adoption or new Lean axioms. The boundary does not cover owned callbacks.

Host receipts record 6G/8G/zero-swap/64-task scopes and current reservations.
Final extraction: exit 0, 4.927 s, peak 671708 KiB, zero swaps. Final resolution:
exit 0, 0.050 s, peak 22220 KiB, zero swaps. Exact command/revision/script and
input SHA pins accompany each receipt. The v2 extraction adds the declaration
signature to the witness for independent attribute checking; v1 is retained.
`#print axioms`: N/A, compiler evidence only. No shipped source/ELF changed.

Source/model identities, full source Calls tree/carriers, final instance/inline
correspondence and the final source-coverage instance are still open. The
current model target is `OraclePortFrozen2.dV_frozen2`; the authoritative headline
is `OraclePortHeadlineFrozen2PerAttempt.final_soundness` (design addendum 13:05).

The strengthened replay initially failed because a naive comma split treated
`initializes((0, 16))` inside a parameter attribute as two parameters. That
failed local check was inadvertently included in the stage-1 commit with the
previous successful receipt. The following corrective commit uses balanced
parentheses and replaces that receipt with the successful final replay:
21 classifications agree, 189 negative controls reject, exit 0, standard
compiler evidence only. No host result or target-flow status was changed.

## Stage 2: strict source CFG chronology and the current std-aware target

`OraclePortS10StrictOrder.before_end` strengthens dominance on a path reaching
its selected target to an explicit occurrence decomposition
`pre ++ cut :: (post ++ [target])`, with `cut != target`. It permits loops
and repeated visits; membership is no longer described informally as strict
chronology. Six generated modules apply the existing kernel-checked cuts to
all 140 source observations (70 distinct graph facts, reused for both builds).
`strict-order-map.json` retains all coordinates and theorem names. The generic
lemma compiled first, then one generated chunk, the other chunks, the std
bridge and one combined import/axioms audit. The first generic elaboration
failure (constructor binder and an unavailable list lemma name) is retained;
its corrected replacement uses the actual Lean `List.append_of_mem` theorem.
No large reduction, numeral evaluation or limit increase was used.

`stage-order.json` maps all 140 facts onto dV_frozen2's actual batch-0,
save/resume, batch-1 schedule. It records the remaining pure-state transport
explicitly: source TX2 runs its twelve query steps after batch 1, while the
model C5 resumer computes those pure steps before batch 1. Source totality,
absence of oracle effects and equality of the reached finish state must be
proved before commuting that computation. Source rejection timing and mutable
state cannot be inferred from the block graph.

`OraclePortS10StdFrozen2.acceptedRunJoin_of_cones` provides the std/allocation
extension's composition endpoint at the **current**
`OraclePortFrozen2Join.AcceptedRunJoin`. Its source/model caller identities,
all fourteen cone joins and S10 coverage remain hypotheses. It does not
instantiate a frozen source tree or discharge either ordering identity.

All nine successful focused targets use only standard axioms and zero swaps.
The std endpoint: exit 0, 15.554 s, peak 3,496,558,592 bytes. Combined
`OraclePortS10Inventory5Freeze`: exit 0, 16.432 s, peak 3,214,852,096 bytes.
Exact targets/commands/revisions, source/import SHA pins, resources and every
new theorem's `#print axioms` line are in `manifest.json` and per-attempt
receipts. This is a focused cached-object union, not a frozen release replay.

## Stage 3: final inline correspondence attempt

Two optimized, capped diagnostic builds enable full DWARF and then
line-tables-only metadata in the selected aspis crates, retaining the frozen
source/features/toolchain. These are diagnostic candidates, never adopted
release ELFs. Full debug: exit 0, 36.042 s, peak 1,097,476 KiB. Line tables:
exit 0, 29.368 s, peak 821,132 KiB. Both report zero swaps and actual
6G/8G/zero-swap/64-task limits. The expected work was optimized SBF
compilation/metadata emission, not an arithmetic gate. The source, commands,
wrapper hashes, resource reservations, outputs and exact ELF SHA/size are
retained in the build receipts and `debug-build-manifest.json`.

**Location transfer is refused.** `debug-comparisons.json` compares every
allocated section and relocation section, including bytes, virtual address,
size, type, flags, alignment and entry width. Both candidates change `.text`
and all subsequent loaded section addresses. Full debug increases `.text`
by 784 bytes; line tables increase it by 832 bytes. Therefore DWARF from
these builds cannot identify frozen final inline instances. No per-mode
expansion is attempted after this failed default preflight. This is a retained
failed correspondence approach, not a source exclusion certificate or an
artifact re-pin. Original frozen ELF evidence remains unchanged. The modified
debug flag and distinct diagnostic target justify the second build; no memory
failure was rerun and no cap was raised. `#print axioms`: N/A.

The pass-4 generic/inline observations remain usable only within their
original compiler-evidence scope. Final inline completeness and concrete
owner adoption are still open.

## Final verification and concrete remainder

`python3 -B tools/s10-inventory5-20261021/audit.py --gates` exits **0** for
packet integrity. `validation.json` records the exact source revision, tool
SHA, resources, nine successful formal results with complete standard-axiom
lines, generator regeneration, all 189 callback negative checks, unchanged
shipped/owned sources, host caps and refused debug transfer. All new code and
Lean sources are pinned in `frozen-sources.json`. No new derived JSON exceeds
5 MB; diagnostic ELFs remain SHA/size-only. No local target directory, key
operation, push, merge, owner-module edit or protected candidate edit occurred.

Both requested completeness gates ran once after the focused generic lemma,
chunks, bridge and combined axioms audit:

- `tools/s10-inventory2-20261021/reconcile.py --check --require-complete`: **2**.
- `tools/s10-inventory3-20261021/reconcile.py --check --require-complete`: **2**.

Exact commands/revisions/script hashes, wall/RSS/swap and full output are in
`gates.json`. Their criteria and scripts were not weakened or changed. Packet
integrity is separate from source completeness. No unchanged full Lean,
runtime, adversarial or SBF release suite was rerun. The two different debug
builds are explicitly failed *diagnostic correspondence* candidates, not a
reproduction or adoption of the frozen release artifacts.

**Target not yet established.** `remainder.json` fixes the exact missing
interfaces. There is still no operational frozen source `Signature`/`Calls`
lowering with complete mutation/errors/allocations; no source or model caller
identity; no final source-coverage instance; no final instance/inline
completeness; and no library/owner adoption or coherent release replay. The
new std-aware two-transaction endpoint retains all these hypotheses. **Zero
semantic caller identities and zero headline premises were discharged.**

The source chronology facts and compiler target flows are established within
their stated boundaries. They cannot be converted into the missing source
semantics by renaming compiler observations or by defining a source interpreter
to equal the model. The next concrete deliverable is the adopted mutable
caller lowering and its path-to-execution relation; its required field/error
carriers are enumerated in `remainder.json` and `stage-order.json`.
