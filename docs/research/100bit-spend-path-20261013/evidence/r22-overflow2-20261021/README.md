# R22 overflow continuation receipts

Stage 1 adds isolated frozen-source contracts for M31/CM31/QM31 decoding,
Reader.raw and Reader.k. No shipped source changes. The generator binds each
copied declaration to frozen revision b2727acd3abf79315d18b754a260f58f4b1c6326;
source-shaped field types are tool context, not a complete extraction proof.

Attempts 01–08: 01 is a compile diagnostic; 02–08 pass. Decoder harnesses
exercise their fixed wire widths (4/8/16). Reader.raw harnesses exercise all
byte values, cursor positions and lengths within a 64-byte backing allocation.
Reader.k is checked over a fixed 64-byte allocation using verified summaries.
**These reader bounds do not cover whole checkpoints.** Contract declarations
have wider domains than those early harnesses: do not cite those early results
as universal verified contracts or use them to discharge R22. Stage 2 narrows
and expands the coverage explicitly. Fixed-width decoder calls in the source
have the tested widths; later contracts restrict those widths explicitly.

Full attempt fields are in attempts/*/receipt.json; summary.tsv is compact.
Exact commands, limits, frozen source revision/hash, dependency fingerprint,
wall, RSS, swaps, errors and the N/A Kani axiom report are preserved. No Lean
theorem or endpoint change is made in this stage, so no premise deletion is
claimed. Sources/ retains small historical tool inputs for coverage audit.

Stage 2: attempts 09–14 cover Reader.raw N=4/16/32 and Reader.k over every
slice length/cursor within a 4,880-byte arbitrary backing array. CM31/QM31
contracts are now explicitly restricted to their actual 8/16-byte call widths.
All these checks pass. 4,880 is a conservative checkpoint bound, **not** the
57,607-byte stored-proof length. Actual checkpoint sizes are 1,768/4,840.

Attempts 15/16 were stopped (exit143) during formula conversion / expansion
of the 256-entry iterator. They are not memory kills or source counterexamples.
The time-command RSS underreports interrupted descendants (2112KiB); use the
also-recorded cgroup_memory_peak_bytes for these attempts. Attempts17/18 replace
the semantic-alpha postcondition's iterator with ten explicit predicates and
reduce CBMC object bits from16 to10. 17 is a CLI rejection (explicit unwinding
assertions conflict with Kani's unwind option); 18 passes, 5.76s/298476KiB.
Safety, pointer and loop-unwinding checks remain enabled. Object exhaustion
would reject verification rather than silently relax the model.

Attempt19 proves the four-statement weight-reader iterator body lifted into
read_one_weight, using Reader.k's verified contract; source/write-order edits
are explicit in the pins. Attempt20 proves the actual frozen update_residue_row
products and flush, with source-shaped M31/CM31/QM31 types, no independent-product
abstraction. It covers canonical power/basis, and row<B+3C for flush or row<B+2C
otherwise (B=2^34, C=(p-1)^2). This is a local contract; downstream row phase and
one-visit traversal still need composition. No endpoint premise is removed.

Stage 3 strengthens the numerical row contract to an exact phase transition.
Attempts21/24/27 are compile diagnostics: Kani's old(row) macro interferes
with the mutable borrow. Replacement adds an unused phase:u64 ghost argument
in the tool copy and supplies terms%4 at the unchanged push call. Attempt28
finds overflow in an *instrumentation precondition* evaluated before phase<4;
attempt31 combines the dependent checks in one short-circuit precondition and
passes. Attempt34 replaces row_bound's four-element iterator with four explicit
comparisons, and passes the same exact arithmetic body. No frozen overflow
counterexample is found by these diagnostics.

Attempts32/35 (variable-size vector push contracts) were stopped for symbolic
iterator/formula expansion. Attempt50 covers all 64-row positions, and passes
using the phase contract. Attempt51 reaches approximately6.1GiB cgroup current
memory during formula conversion and is stopped before the high watermark;
the replacement partitions the 256-row position space into four syntactically
six-bit offsets, with unchanged limits. These checks are source-shaped exact
body replay plus the explicit unused ghost parameter, not ELF equivalence.

The new R22OverflowContinuation2Cadence Lean module proves step safety,
induction over an arbitrary list of bounded products, pointwise row lifting,
and the exact checkpoint cursor schedule. First compile fails because an
unreduced let hides the arithmetic from omega; second changes to dsimp only
and passes (1.11s,836993024bytes). All four successful axiom lines contain
only standard axioms. Failed compile diagnostic lines containing sorryAx
are retained as failed evidence, never accepted as proofs.

Attempts36–47 and49 establish source-bound contracts for the actual field
reducer, scalar add/sub/neg/double/mul/reduce, CM31 construction/multiplication,
the checked fibre-index constructor (macro expansion), immutable table access,
fibre-point and line-node functions. Every downstream arithmetic harness uses
stub_verified for its proved child contracts. Attempt48 is a setup failure:
Point needed an Arbitrary derive for verified stubbing;49 supplies it and
passes. The enabled field branch is the non-r0-r91-audit branch; no build
feature or syscall correspondence to the frozen ELF is claimed.

Stage 4/final: contract-index.json selects the accepted contracts and explains
all domains/dependencies; remaining-summary.tsv identifies the concrete missing
joins and references the unchanged exact prior OPEN site IDs. 75 Kani attempts
include51 successful attempts/43 distinct targets. Four new Lean theorems pass.
All successful standard-axiom lines are preserved in the focused Lean receipts.

The256-row push proof uses Z3 after SAT formula expansion; all four index
partitions pass in11–13s at approximately538000KiB RSS. Object-bits8 diagnostic
attempts reject with too many addressed objects; object-bits9 does not cure SAT
formula size. No cap is raised. Source field contracts extend to concrete
QM31 and WideExact operations and strict WideExact decoding. Decoder Reader.e
and the composed Merkle caller pass with CaDiCaL after Z3 internal map::at
failures. The Merkle suffix scan ignores the overwritten/dead prefix, and the
composed caller still assumes legal i/w: it is not a whole frontier proof.

Attempt108 is an expected diagnostic: the actual owned-Vec-return weight reader
cannot be used by stub_verified because its return type lacks kani::Arbitrary.
Attempts106/109 additionally retain the stopped variable-length loop / fixed64
SMT internal error. The complete weight loop remains open. boundary-status.json
records the missing FunsExternal source and unchanged endpoints verbatim.
No failed compile, diagnostic target or conditional local contract discharges R22.

Run generate.py --check and audit.py for read-only validation. Never run all
harnesses as a regression: historical bounded tests and deliberate failing
API diagnostics are retained, and a full suite would repeat unchanged work.
