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
