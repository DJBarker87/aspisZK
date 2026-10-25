# D189 history consumer

`RowOrder_History.on_d189_cuts` checked in attempt RowOrder-004, source
revision 143ffa1803 with dirty new sources (exact SHA in receipt). It consumes
the same FirstCut/SecondCut/SourceCuts exported by D189; it does not generate
another existential execution. It inverts the actual accepted first wrapper,
derives the destination size from source acceptance, proves the committed
post1 payload is the returned saved Vec, and reindexes the runtime history.
The resulting CheckpointVersionBinding retains exactly the input runtime's
key, ledger and event list. Writer/reader header authentication and P2Prime
then give the same loaded checkpoint, proof and public bytes and size1768.

Retained premises: actual accepted first wrapper, canonical exported cuts,
TrustedStd copy, allocator/extraction dictionaries, writer/reader child ports,
CheckpointVersionBinding on actual post1, and P2Prime on the actual cuts.
Runtime history protection is NOT proved. This is a consumer for D189's
traced witness, not a new accepted-pair trace-existence theorem, a headline
join, or a deployed result. No cryptographic assumption is discharged/added.

Validation: four focused Lean attempts, no Kani/Rust. 001 failed missing State
namespace plus elaboration depth; 002/003 failed projection elaboration depth.
The repair split symbolic projection lemmas; no resource options changed.
All failed elaborations/automatic sorryAx outputs are excluded from evidence
of closure. 004 exited0 in1.744128669s, peak4409328KiB, swap0. New projection
theorems have no axioms; on_d189_cuts uses only propext/Classical.choice/
Quot.sound. Exact command, source hashes, direct dependency hashes, cgroup,
wall/RSS/swap and complete axiom/statement output are in RowOrder-004/.
All runs used6G high/8G max/swap0/tasks64 and -M7000.

Budget4/100 Lean,0/60 Kani. No shipped/cfg(kani) files changed. Next deliverable:
exact frozen2 read-order normal form; raw dictionary-to-frozen2 remains open.
