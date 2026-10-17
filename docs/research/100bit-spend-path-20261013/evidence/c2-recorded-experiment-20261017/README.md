# Recorded-experiment C2 compiler component

`C2RecordedExperimentConstruction` checks the accepted design's second path at
model level. `compile` records the entire original prover-plus-byte-verifier
experiment and constructs auxiliary words using `RawCutWordsFromView.buildWords`.
Its four results show the row2 `.c2` constructor carries the constructed word,
that word is the C2 map at the actual model commitment cut, and the compiler
preserves the public statement, byte-verifier acceptance and total distinct
first-read count.

This is **not an actual Rust execution bridge**. No complete actual prover+
verifier witness is supplied by this checkpoint. No saved verifier-only counter
is used as one. `word_from_actual_cuts` refers to the actual *model* chain
inputs and the full model log. The total recovery map may default missing
coordinates to zero; this does not assert equality to the whole honest host
word or recovery of all2^20 indices from22 openings.

The source requirements remain explicit:

- `Backend::c2` and `Commitment::build` must be connected to actual successful
  owned H1/G→coefficient→encoder-result executions; their retained extraction
  blockers are in the earlier C2 owned-host checkpoint.
- The Rust hash callback call shape (`HashFn`, `Digest32`, `LegacyHashFn`) does
  not prove purity or oracle semantics. A source execution relation must record
  every chronological prover and verifier call, its exact concatenated bytes
  and returned digest, and coherence with the model oracle. The call type alone
  supplies none of these facts. The admitted program's callback and arbitrary
  prover calls must both be covered.
- Actual accepted Rust execution must supply the strict decoded messages,
  exact row0/2/30 constructors/roots and frame correspondence. The subsequent
  full-log recovery theorem additionally needs the complete first-read budget
  and the shared collision exclusion. Those existing theorem premises remain
  open, not discharged by these four results.
- Installing auxiliary metadata preserves erasure and byte sampling; semantic
  reading additionally needs the same constructed word in row2, successful
  full25 decoding/read and typed caller context. Packing/salts/path custody
  and checkpoint authentication stay independent.

Executable mapping is explicit: this file's `compile` is definitionally the
existing `RawCutProverCompiler.compiled` with its `buildWords` argument fixed to
`RawCutWordsFromView.buildWords decoder`. `row2_constructor` reduces that exact
model evaluation and `RawCutTranscriptRun.proof`/`enrichMessage`; it does not
rename a Rust constructor. `word_from_actual_cuts` projects the existing checked
`buildWords_eq_actual_cuts`; the preservation results instantiate the existing
compiler lemmas. None of these definitions is a production Rust function.
The exact Git source/hash inventory for the production origin and these model
constructors is `evidence/c2-owned-host-20261017/source-inventory.json` and the
accepted `design/J1-C2-LITERALMESSAGE-SOURCE-DESIGN-20261016.md`.

| Exact target | Attempt | Exit | Wall | Peak RSS KiB | Swap | Axioms |
|---|---|---:|---:|---:|---:|---|
| `C2RecordedExperimentConstruction` | recorded-a | 0 | 2.794s | 3,626,780 | 0 | 4×`[propext, Classical.choice, Quot.sound]` |

Source base `6bd624b3960aa699333fadd00fa498b468e5e887` (receipt records its unique
short ref `6bd624b39`), exact changed source SHA
`d8044957171dadf6fa100670a8a5417f9056a19dbf257b4152981f5508013df0`.
Existing pinned Lean4.32 imports; `lake --no-cache env ... lean -j1`, no dependency
rebuild. Cap6GiB high/8GiB max/swap0; aggregate reservation39,057,358,848bytes
below55GiB. Same-launcher external precheck and200ms monitor found no overlap.

Archive `recorded-experiment.tar.gz` SHA
`ef8f53f1f4fecd12a974f997653c7a9be1c930c1616e29a07c3fad03bc32149f`
contains11 exact source/object/runner/environment/manifest/log/receipt files.
`recorded-members.json` pins every member; kit `check-recorded.py` is read/hash
only. No new Rust source, SBF, runtime harness, native gate, live worktree or
module changes accompany this component.
