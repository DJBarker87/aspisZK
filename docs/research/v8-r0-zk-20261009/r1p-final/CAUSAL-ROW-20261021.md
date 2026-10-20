# Causal row: interface obstruction and bottom-up facts (2026-10-21)

Branch: `codex/cx-priv-causal-20261021`; base `8abe236f2`.

Status: **R_causal_D80 remains open.** The requested conclusion cannot follow
from execution order alone for the actual parameter interfaces. The common
rules §4 require stopping a false target, recording its counterexample, and
continuing independent items. No change was made to `PrivacyR1Final.lean`.

## Checked counterexample

`R1Z/CausalOrderObstructionBin.lean` defines `prematureC2 W` by changing only
`W.frame` to `fun _ root _ => ans root`. This is a valid `R1Wire`, but not the
protocol encoding. Its row-zero absorb reads C2's root regardless of the view.
`prematureC2_not_causal` proves:

```text
¬ ord⁻¹(C2 root) < ord⁻¹(absS 0)
    → ¬ RCausal (prematureC2 W) Pr h B outputs x w
```

The proof uses two arbitrary answer vectors, differing only at C2's root
(zero versus the constant-one digest). They agree at every predecessor of
row zero, while row zero's address differs. No collisions, successful cuts,
operational run assumptions, or nonstandard axioms are used. This obstruction
also survives specifying the commitment address grammar: the contradiction
uses only a transcript address, with no constraint on `Pr.caddr`.

The protocol order puts C2 after rows 0–1 and before row 2. Consequently it
satisfies the theorem's `late` premise. No choice of that protocol order can
make this admissible wire causal. Ordering C2 before row zero would instead
violate the requested protocol schedule.

## Missing model restrictions

The D48.3 prose says that phase conditions are fields. Inspection of
`R1Z/GamesR1PBin.lean:92` shows the actual `R1ProverP` has `caddr`, `leafVal`,
`tapeOf`, opening data and `ord`, with no such fields. The roots in `attAddr`
are coordinates of the arbitrary answer vector, not a phase-restricted
`commit` function. Separately, `R1Z/GamesR1.lean:61` imposes no restriction on
which rows use the root argument of `frame`/`payload`, or which challenges
`dec` places in each decoded component. The complete view passed to these
functions contains `outputs x ch` (`R0Z/JointView.lean:31`), and `leafVal` can
read the entire challenge record.

Thus a complete next implementation needs a concrete, phase-restricted
model encoding and leaf-value construction, plus proofs of its row-local
noninterference at **all** answer vectors. In particular:

- C1 leaves use no transcript challenge; C2 leaves use only rows 0–1;
  folded leaves use only rows through 29.
- Frames use C2 only at row 2, payloads use folded only at row 30; all other
  view/auxiliary bytes use only challenges available at their row.
- Decoded challenge components obey their squeeze-row dependencies;
  QueryScan selection uses the earlier query blocks.
- Both expander streams precede all tape-dependent consumers; bindings,
  seeds and salts obey the grammar dependencies; the concrete total order
  refines those relations without enumerating the enormous position universe.

An appropriate eventual source hypothesis is
`R10_RWire_executes_phase_order`: the normalized source hash-call trace
executes the constructed model's total order, preserving addresses and
answers. This is a **proposed interface name**, not a proved or installed
Lean hypothesis. The evidence handoff is LOG D80/D81/D82 and
`r1p-premises/PREMISES-20261020.md` (ordered-log row and closing discussion):
R10 common backend/log consistency together with R-wire/R13 normalization
and source-loop correspondence. Those records explicitly leave execution
joins open; they do not already establish the new hypothesis. Merely naming
this source fact cannot supply the missing model noninterference facts.

## Independent binary-tree progress

`R1Z/CausalTreeOrderBin.lean` proves symbolic dependency-layer inequalities:
salt before leaf, each non-root binary child's layer before its parent,
and both root children before root layer 24. `shared_parent` identifies the
ranked parent's address with `SharedBinaryRecordGrammar.nodeInput` through
the existing bridge. The proof splits the depth index at zero/successor;
it neither enumerates nodes nor evaluates a concrete tree recurrence.
These are partial order facts, **not** a constructed `Pr.ord` equivalence or
an RCausal proof. The 33-row schedule proof and final integration remain
unimplemented pending the phase-restricted model.

## Verification and exact disposition

All compiles used the build host, `run-joint.sh`, environment J, limit
7000 MB, cgroup MemoryHigh=5G / MemoryMax=7G / MemorySwapMax=0. Existing
shared source/object files were not overwritten; only the two new module
paths were added. No package or frozen-manifest replay was run: no final
causal bridge exists to release. No source/runtime suite was needed.

| Attempt | Target | Exit | Wall | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| 8800 | CausalOrderObstructionBin | 1 | 2.08 s | 3502864 | 0 |
| 8801 | CausalOrderObstructionBin | 1 | 2.04 s | 3502968 | 0 |
| 8802 | CausalOrderObstructionBin | 0 | 2.19 s | 3521720 | 0 |
| 8803 | CausalTreeOrderBin | 1 | 2.88 s | 3495384 | 0 |
| 8804 | CausalTreeOrderBin | 0 | 3.05 s | 3513648 | 0 |

8800/8801 failed on the final list-reader rewrite; 8803 used `rfl` for a
strict inequality and was replaced by symbolic simplification. Each retry
changed source. Failed audits containing `sorryAx` are retained as failed
attempt evidence, never accepted as theorem evidence. The final audits of
all five theorems use only subsets of `[propext, Classical.choice,
Quot.sound]`. Complete stdout, errors, timing, source SHA/revision and
import-object SHA fingerprints are in `causal-attempts-8800-8999.jsonl`.
`run-causal-attempt.py` records one focused attempt at a time.

`PrivacyR1Final.lean` before/after: **identical**. In particular the original
universal Earlier/attAddr premise remains. No strictly weaker sufficient
premise was established, so no replacement is claimed. The work proves an
interface obstruction and four independent tree facts, and does not claim
to discharge the definition-of-done row.
