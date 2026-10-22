# Prover commitment continuation 32

Base: 26b922be6. Branch: codex/cx-prover-commit32-20261022.
Work in progress. Target not yet established.

D143/D144 govern this continuation: sorted owned association lists and small
recursive extracted functions; public statement bytes, submitted proof bytes,
and answers to adversary queries are the observable. Timing and other side
channels are outside the privacy contract. Internal programming tables and
attempt counts are not published protocol outputs.

Stage 1 starts with sorted numeric-map insertion, lookup and query-order
publication. These are proof-only references; no native-owner equality is
claimed merely by adding them. The remaining stages are the complete
publication driver, eight-attempt owner, real entropy/reservation owner,
source-to-FSExperiments conversion, both WholeRunJoins and deletion-only
endpoint specialisation. RustProverRefinement remains explicit.

Recovery stage: the in-flight Kani process survived the capacity interruption;
its existing capped run is being collected before a replacement is considered.
The three small roots (`index_insert`, `publish_queries`, `merge_program`)
translate with `has_errors=false` and Aeneas exits 0. The generated import
`Aeneas` is mapped to the pinned env J imports `Aeneas.Std` and
`Aeneas.Tactic.RustAttributes`, as for the prior continuations.

Env J 9021–9024 compile the insertion and query-publication generated modules.
Attempt 9029 proves `R1Z.ProverCommitPublication32.next_cursor` and
`lookup_total`: every finite table lookup from an in-bounds cursor terminates
without an indexing error. This is totality, not yet the sorted-map refinement.
Both print `[propext, Classical.choice, Quot.sound]`; exit 0, 1.37 seconds,
2,533,728 KiB peak RSS, zero swaps. Rejected attempts 9025–9028 are retained.
Exact source snapshots, hashes, dependency fingerprints and compiler logs are
in `evidence/prover-commit32-20261022/lean/`; extraction/Kani logs and source
pins are beside them. No endpoint premise has been removed.
