# Candidate 14: fixed two-run S2 Libra factorization

**Actual old/new source helper equality and unchanged caller-context substitution
are checked with concrete source arithmetic.** Candidate
`39c2971dd16c95858a4cfd2c9ae35da052eacfa9`, exact parent
`16724ebd0bc2cb38f0115681386ecb4f12ceddc7`.

This justifies the retained **33,363–33,427 settlement CU** saving, with no
stage-1 saving. It adds no further measured saving. Production Rust, transcript,
challenge schedule, public input encoding, proof/checkpoint bytes and runtime
artifact are unchanged. Existing codec/583-call trace/checkpoint23/injection,
strict SBF stack audit and six-fixture CU results are reused from
`../cu-savings-20261019/FINAL-REPORT.md`; Lean edits did not rerun those suites.

`CuSavingsLibraCandidate14.kernel_equivalence` compares the entire emitted
parent `twofold_libra_weights` and new `factored_s2_libra_weights`, yielding
**identical source field arrays**, rather than merely equal decoded values.
The old reference follows both complete 28-power builders (including their
unused final multiplication), all sixteen cells in each of four blocks and
all source checked indices/divisions/remainders/skipped inactive cells. The
new source proof consumes its actual four-power builder, square/multiply
chain, scalar-factor fold, four-term constructor, prefix sums, both branches,
array updates and exact two-iteration source loop plus termination.

The existing symbolic semiring proof establishes the 28=16+12 cut and fresh
exponent origin of the next run. Concrete current-source arithmetic proves
canonical successful field operations and their interpretation in the exact
quadratic tower. Canonical decoding injectivity turns the algebraic identity
into equality of actual output carriers. The concrete
`production_equivalence` and `caller_context` theorems have **no assumed
candidate equivalence or arithmetic laws**, and no `Arithmetic`/`Shared`
parameter. Actual source low16 construction discharges its canonicality and
coefficient decomposition. Arbitrary common before/after computations preserve
all their errors and divergence.

The production theorems retain canonical ap0/ap1 and extra-challenge premises.
Their use is the existing reference canonical-field input boundary: actual
powers, sampled challenge origins and strict checkpoint e/k decoders must
supply it. The integrating source-origin specialization is tracked separately;
this report does not assert equivalence for arbitrary forged raw `Weights` or
field carriers. The complete `Weights.pair` source is byte-audited: its sole
change is the S2 helper-selector expression. No separately re-extracted whole
transaction or full soundness/privacy transfer is claimed.

Exact source extraction exposed a producer/backend mutable-closure signature
mismatch. Four original emitted callback bodies are preserved byte-for-byte.
Six explicit runtime signature projections select the emitted call_once,
apply its original mutable handback, project the FnOnce value, and preserve the
mutable builder's final captures before the source caller discards its unused
second result. Kernel handback/projection proofs and the existing complete
source `array::from_fn` admission support these adapters. There is no new
source-prefix interpreter or opaque equivalence axiom.

One final topological replay aligns the changed proof dependency objects.
The selected receipt audit checks **29 Lean targets**, all current source
hashes and selected direct-import object hashes. Every selected axioms result
contains only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or
native-decide axiom is admitted. The final bridge took **2.004 s**, peaked at
**2,974,816 KiB RSS**, and recorded **zero process swap**. Commands, features,
revision, wall time, RSS, cgroup/process swap, actual foreign-job lists and
axioms outputs are in `LIBRA-CANDIDATE14-FINAL.json` and individual receipts.
Small focused jobs may overlap other explicitly authorized team jobs; no
exclusive-host timing claim is made.

`check-libra-candidate14.py` reproduces the source/receipt audit.
`LIBRA-CANDIDATE14-DECLARATION-REPIN.json` follows the Digest32 inventory format
for the new helper and changed `Weights.pair` dispatch, with source byte ranges,
file/fragment hashes and extracted declarations/consuming bridge names.
`libra-emission-provenance.json` pins actual Charon/Aeneas binaries, LLBC and raw
emission hashes, and explicitly corrects descriptive metadata inherited by one
historical extraction plan. No ELF, shared object or Lean object is committed.
