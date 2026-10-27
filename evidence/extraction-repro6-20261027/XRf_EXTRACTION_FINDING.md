# Call-closed six-leaf extraction: release claims failure

**Target not yet established. Actual top premises removed: 0.**

The selector exclusion error inherited from XRe is removed. The final LLBC is
`289362adfae8a53aa1d5e1ae491ee2d682a7df1db0308cba4206b1629c79e671`,
17,346,679 bytes, has_errors=false. The same pinned release snapshot
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, built MIR,
private-leaf-salts feature and Charon/Aeneas binaries are used. Each Charon run
rehashes all 7,978 source files successfully. No shipped source, translator,
library or LLBC patch; no added release opaque selector.

## Call closure before Aeneas

XRf_001 changes Iterator::copied from excluded to declared opaque, retaining
its signature. This fails Charon's trait-reference check for IterMut and
Enumerate (has_errors=true); rejected, never supplied to Aeneas.
XRf_002 adds Charon's documented `--duplicate-defaulted-methods` option. This
resolves those binder errors, but duplicates the library PartialEq::ne default
as an opaque synthetic transport::Variant method. XRf_003 explicitly includes
`core::cmp::PartialEq::ne`, preserving its body. This final artifact has exactly
the original six release-namespace opaque functions: checkpoint, check_values,
echeck, expand_values, candidate::wide_view and prepared_claim.

`XRf_closed_release_candidate_tx1_inventory.json` lists every callee of every
translated body, caller/body hashes, names, spans and declared/builtin/parameter
status: 544 function entries, 1,545 calls, zero missing/unclassified callees.
Calls resolve to 321 translated entries, 794 opaque declarations, 400 translator
builtins, 29 declared trait-parameter calls and one typed observer function
parameter call. These are call-site counts, not distinct callee counts. The
last two kinds are explicit polymorphic runtime inputs; declaration closure is
not a semantics proof. Library opacity is visible and distinct from the six
release leaves. All library items actually called are present, including
Iterator::copied. The fourth invocation asserts this inventory and six-leaf
gate before invoking Aeneas. The inventory is produced before that invocation.

## Exact new obstruction

XRf_004, pinned Aeneas, exit **2**, wall **34.990505011 s**, peak RSS
**1,376,348 KiB**, swaps **0**. Full raw trace: XRf_004/stdout.log, lines3650 onward.

Failing function: **aspis_r1_cost_probe::r1_semantic::claims**, a **release item**,
not a library item. LLBC function383, whole declaration span r1_semantic.rs42–55,
structured-body SHA256
`bee183acbeb2d009d4b83a5e60a15529a49c7bed49b8060e36be3aa6a232de9b`.
The reported failing source region is **r1_semantic.rs47:8–55:1**, the loop that
writes three decoded29-element rows into a MaybeUninit Box and assume_init.
Compiler source: **interp/InterpReduceCollapse.ml:1880**,
`add_shared_borrows.update.update_avalues`, reached through loop context join/
collapse. Aeneas reports `Internal error, please file an issue`.

This is the first newly exposed failing release body after call closure, beyond
the six approved opaque leaves. It is not a counterexample to the Rust function,
and does not authorize making claims a seventh opaque leaf. Extraction runs
stop here, as instructed. **No Types, Funs or other output file was emitted**;
XRf_outputs.json records the empty list. No complete Lean kit or release
association exists. No fabricated carrier or successful-return contract is added.

## Budget and next deliverable

Combined invocations **4/4** (three Charon, one Aeneas), all terminal in separate
scopes with6G high/8G max/swap0/tasks64. One scope at a time, no cap raise,
timeout, memory kill or unchanged failed-input retry. Exact command, configuration
source snapshot/hash, dependencies, revision, exit, wall, RSS, cgroup peak,
swap and raw error/axiom applicability are in each receipt. `#print axioms` is
N/A for extraction, and no Lean proof is claimed.

Next: lead decision on a focused claims extraction repair/reference route with
unchanged source semantics; then complete emission and concrete association.
No further extraction run is authorized in this round. Top and ledger remain
unchanged; no release conclusion, formatter reachability, joint top
non-vacuity or source-to-ELF correspondence is established by this artifact.
