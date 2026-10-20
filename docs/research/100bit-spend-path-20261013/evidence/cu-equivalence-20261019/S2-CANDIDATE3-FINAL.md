# Candidate 3: fixed S2 inactive groups — source equivalence checked

Candidate `d631a90ec0b75d2efbeaf62b7ee9c1ba9aac7ffe` is checked against its exact
parent `ad5bf503319b90d152baaa1dfb5c037d278eb4bd`. Retained measured saving is
**40,517–40,520 settlement CU**, zero stage-1 saving, across the six fixtures.
The production source and ELF were not changed for this proof.

`CuSavingsS2Candidate3.helper_equivalence` proves unconditional equality of
both complete emitted `grouped_inactive_pair` helpers. The S2 fast path derives
its exact classification from the actual `Weights.raw`, permutation, active
row masks and inactive lookup; the 64 blocks, 12 masks and first-occurrence
order match the old dynamic search. A prefix invariant relates the old
64-element coefficient array to the new 12-element array. The coefficient
and weight/add/multiply calls occur in the same order. No arithmetic
reassociation, canonical-input, decoder-success, termination or kernel-
equivalence premise is assumed. Failures and divergence are preserved.
The fallback is equal for non-S2 and every wrong-length input.

`all_callers_equivalence` proves substitution into any identical computational
context. The audit pins the unchanged Rust `Weights.pair` and
`verifier::finish_relation` source and their consuming call sites. These
contexts are not claimed to be separately re-extracted transaction bodies.
Both changed helpers remain byte-identical at frozen production revision
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`.

## Verification and remaining boundary

21 focused Lean targets passed; 13 unchanged table certificate objects were
reused after source/object/receipt hash checks. Accepted target compilation
totalled 41.50 seconds; maximum peak RSS was 2.43 GiB, with zero process swap.
The final bridge took 1.604 seconds, 2,410,588 KiB peak RSS, zero process swap.
The full exact commands, revisions, features, cache/import hashes, exit
statuses, wall times, RSS, swap and `#print axioms` outputs are in
`S2-CANDIDATE3-FINAL.json` and the selected run receipts. No selected run
launched with a foreign Lean job. Failed intermediate attempts are historical
and excluded from the accepted closure.

The final axioms are `propext`, `Classical.choice`, `Quot.sound`, and inherited
`core.fmt.Formatter`, a Type-valued runtime boundary. There is no `sorryAx`,
native-evaluation axiom or candidate-equivalence axiom. The `Shared` interface
contains only computations; it assumes no algebraic or success propositions.
An initial derived Debug-format extraction introduced native string-length
axioms; it was rejected. The accepted source emission treats that unchanged
formatter as a shared computation, which `unwrap` does not inspect.

The existing Rust/Charon/Aeneas translation and coherent primitive/runtime
semantics, with sufficient stack/resources, remain the reference boundary.
The accepted emission uses the previously pinned opt-in no-branch-join
frontend; interpreter/type/borrow checks remain enabled. Raw Types is unchanged;
raw Funs receives only a shared-instance binder. `s2-emission-provenance.json`
pins the producing tools, LLBC and raw emissions. No LLBC, compiled Lean
object, ELF or shared library is committed.

The source/receipt audit is reproducible with:

```
python3 docs/research/100bit-spend-path-20261013/tools/cu-equivalence-20261019/check-s2-candidate3.py
```

It also checks the extraction/emission generators, production-source freeze,
direct import object hashes, reused table certificates and the Digest32-style
declaration re-pin inventory for both changed functions. The final JSON records
the audit's own command/revision/features/exit/time/RSS/swap.

This proves one replacement under that boundary; it does not close the whole
combined soundness/privacy transfer. Candidates **6, 12, 4 and 3** are now
closed: **4 of 10 retained optimizations**. The next largest remaining measured
saving is candidate 1 gamma reuse: **34,201–34,243 stage-1 CU**.

Existing codec, ordered-hash-trace, checkpoint, injection, stack and six-fixture
CU evidence is reused from `../cu-savings-20261019/FINAL-REPORT.md`; no covered
production source or artifact changed. Worst measured values remain
1,199,687 stage-1 CU and 1,188,496 settlement CU. These are fixture measurements,
not a universal compute bound. No protocol, public-input, checkpoint or proof
encoding changed.
