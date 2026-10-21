# Parser and multiproof source refinement

Assigned branch: `codex/cx-multiproof-cone-20261021`. The oracle-decision port
is approved for this work. Target: `OraclePortHeadlineFrozen` at
`OraclePortFrozenOrder.dV_frozen`, not the superseded recursive schedule.

## Stages

1. Pin actual parser, compact codec, leaf-batch and binary-level source cuts.
   Keep shipped files unchanged. Generate proof-only copies with an explicit
   substitution ledger; compare owned transitions under Kani.
2. Extract owned references using pinned Charon/Aeneas, preserving row and
   level recursion. Prove their mathematical meaning in new Lean modules.
3. Compose through height 18, parser sections and the reached caller, retaining
   ordered oracle addresses and ordinary rejection. Audit the exact residual
   before changing the cone classifications.

## Proof boundary

A passing one-step certificate is not a whole-loop certificate. Equality of
roots is not equality of ordered oracle logs. The scratch suffix and writes
made before rejection must be retained where observable in the source cut.
The global `AcceptedRunJoin` still requires the other cones and the frozen
source/model caller identities. No whole cone is declared complete here yet.

## Resources and evidence

Host workspace: `/home/dombarker/project-offloads/codex-cx-multiproof-cone-20261021`.
Host jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 after
reservation preflight. Rust gates are optimized. Local Lean uses one process,
the shared mkdir lock, `-j1 -M4400 -DElab.async=false`, and a private object
folder. Every compile/proof attempt records target, revision, source/dependency
hashes, exit, wall time, RSS, swaps, and axioms (N/A for Rust).

## Owned reference and first focused proofs

The source-cut generator and all references are proof-only. No shipped crate
was edited. The original conditional tuple in binary_step failed Aeneas borrow
collapse at InterpBorrows.ml:2731; the replacement returns through an owned
write helper. Conversion unwraps were removed to avoid Formatter. The full
parser's first translation exposed external slice/array equality and Vec.extend;
its replacement uses explicit header bytes and an owned row accumulator.

The binary reference translates and its generated Types/Funs compile.
`MultiproofConeCodec` proves total strict-word evaluation, exact agreement
with `OraclePortCompactDraft.rowShape` on all reached rows, and exact compact
value expansion with a zero high half. All three axiom reports are standard.
Full parser-to-parseReached equality and the source joins remain open.

Ten parser/key Kani roots passed (parser-local-2: exit 0, 88.527 s,
2,780,960 KiB RSS, zero swaps). These are primitive predicates/offsets,
not the complete scanner or Prefix caller. Subsequent reference changes
require current dependent certificates. Native-1 passed; native-2 exposed
a missing Debug derive on the proof-only copied error carrier.

Multiproof-step-1 diagnosed memcmp unwinding. Step-2 was stopped to use
arbitrary independent observation coordinates. Step-3 proved leaf insertion
and missing-sibling rejection, but the sibling group timed out at 240s;
the suite was stopped after that diagnosis. Step-4 observes one universally
arbitrary oracle-input byte instead of constructing a full event buffer;
call count and all component lengths remain checked. The complete certificate
is pending. No intermediate check is a whole-cone AcceptedRunJoin.

## Current local step certificates and recursive reference facts

The general symbolic roots now pass; ordinal diagnostic roots have been
removed. Final certificates retain arbitrary arrays, n/i/w and node cursors,
not merely a preflight at i=0. The verified `read32` contract requires exactly
32 bytes and equates every returned byte to its input. `binary_sibling_group`
uses only that verified stub. Callback observations check every component
length, call count and a universally arbitrary address-byte coordinate; the
returned digest and scratch are checked at universally arbitrary coordinates.
No entire tree is unrolled by Kani.

* `multiproof-current-1`: all five roots pass, exit 0, 80.283 s,
  741,520 KiB peak RSS, zero swaps.
* `parser-current-1`: all ten field/key roots pass, exit 0, 48.538 s,
  3,291,276 KiB peak RSS, zero swaps.
* `leaf-layout-2`: three roots pass, exit 0, 15.164 s, 563,692 KiB
  peak RSS, zero swaps. The count-group body is generated from the actual
  node_count loop with Arity::Two fixed and its reference qualifier adapted.
* `native-3`: all four optimized differential tests pass, including full
  accepted binary verification, partial rejection scratch and the complete
  compact parser under framing/canonical/salt/root/node mutations.

The failed Kissat/JSON runs are retained. The last diagnostic preflight
reached MemoryHigh throttling in the Kani driver (not an OOM or cap increase);
it was stopped. Borrowed observation buffers, verified byte-reader stubbing,
CaDiCaL and text output resolved the general symbolic cases. Assertion
reachability cover checks are disabled in these final runs; correctness,
bounds, overflow, explicit contract preconditions and unwinding checks remain
enabled. Nonempty witness domains are n=2,i=w=at=0,idx=[0,1,...] for the
occupied case; n=1,i=w=at=0 with 32 sibling bytes or zero bytes for the sibling
and short cases. Array contents and observation coordinates remain symbolic.

`MultiproofConeLeaf.leaf_step_total` proves outer-success of the actual
extracted insertion whenever n<16, retaining inner unequal-duplicate failure.
`digest_eq_total` proves exact 32-byte equality. `MultiproofConeWordScan`
proves total checked word scanning against a structural list recurrence on
arbitrary input lengths. `MultiproofConeHeight.height_total` inducts over the
actual extracted height recursion up to 18; its RowJoin still needs the
concrete frontier/scratch invariant. Its conclusion concerns returned values,
not source log equality. These are standard-axiom focused facts, not whole
source-cone joins.

The complete compact parser reference now translates without any generated
external declarations; its Types/Funs compile. The reference source differs
from the retained binary extraction only by cfg(kani) reader-contract
attributes, which are absent in extraction builds. A final combined run is
needed after adding the exact count-group/leaf source cuts.
