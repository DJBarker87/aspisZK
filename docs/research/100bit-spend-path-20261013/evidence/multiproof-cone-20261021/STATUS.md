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
