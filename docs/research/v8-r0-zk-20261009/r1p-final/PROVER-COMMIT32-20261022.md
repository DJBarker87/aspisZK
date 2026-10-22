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

The focused recursive proofs now also establish:

- `lookup_refines`: exact early-stop sorted-list lookup for all finite tables;
- `publish_refines`: exact query-list order, including repeats, absent entries,
  and the unchanged byte-append failure behavior;
- `tail_refines`: tail copying equals prefix concatenated with the unprocessed
  suffix, under the explicit capacity bound;
- `insert_refines`: exact ordered-list insertion, replacement and returned old
  value for all finite tables under the explicit capacity bound.

The pure-list specifications are definitions in the proof modules, not assumed
successful source calls. Sortedness/map correspondence is a separate obligation:
these theorems alone do not certify the native BTreeMap owner. Accepted focused
checks are J9032 (publication), J9034 (tail), J9035 (generated programming module)
and J9038 (insertion). Axioms are subsets of `[propext, Classical.choice,
Quot.sound]`; all accepted checks exit 0 and report zero swaps. J9030,
J9036–9037 are rejected proof drafts, retained with exact errors.

The recovered insertion v5 completed with exit 124 at 600.105 s and a
6,594,351,104-byte scope peak, zero swaps. Lookup v1 likewise timed out at
600.161 s with a 6,631,309,312-byte scope peak. These are not accepted Kani
results. The revised gate constructs a sorted pre-state directly; the selected
observation variant compares a universally selected entry and byte instead of
whole-map/vector equality. Unwinding assertions remain enabled. No cap was
raised and no unchanged full regression was repeated.
