# QueryScan: ordered model, exhaustion and the pinned source boundary

Base: `a0b0aebb874dca71170d80574e4fde6a1a0441a1`.
Branch: `codex/cx-queryscan-20261020`. Frozen verifier source is unchanged.
Paths below are relative to `docs/research/100bit-spend-path-20261013/`
unless prefixed with `crates/` or `docs/research/v8-`.

## Result and scope

The model-side exhaustion bound is proved in Lean:
`QueryScanModelFailure.exhaustion_bound` gives probability at most `2^-454`,
hence below `2^-100`, for 64 independent uniform 18-bit words. The model
also preserves stable first-occurrence order, emits 22 distinct indices on
success, and agrees between block scanning and the flattened word stream.
Finite coupling and union-bound lemmas specify the additional abort charge.

**R4 source closure remains open.** The pinned `QueriesModel.Boundaries.decode`
is an arbitrary operation. A checked countermodel below shows why universal
source distinctness cannot follow from this interface. Existing stronger
candidate theorems still require the production iterator/driver correspondence.
No candidate was adopted, no frozen Rust was modified, and no end-to-end
source/ROM or privacy theorem is claimed here.

## Source map and exact order

The sampler is actually in `crates/aspis-core/src/r0_transcript.rs`, imported
by the cost-probe transcript. The cap is **64 words in eight blocks**, not
64 blocks/512 words. Constants: lines 46–48. `query_words` at 186–188 parses
consecutive four-byte little-endian words and masks each with `2^18-1`.
The first candidate is bytes 0..3, the eighth bytes 28..31; block order is
0..7. Uniform 256-bit blocks induce eight independent uniform 18-bit indices:
each low-18-bit value has exactly `2^14` preimages in a 32-bit word. This
byte-distribution transport is mathematical source analysis here; it is not
an additional proved source-to-ROM theorem.

`QueryScan::scan` (202–214) checks completion/cap **before** each word,
increments draws, tests membership only in `accepted[..accepted_len]`, and
appends fresh values. Zero-filled unused capacity is not part of the dedup
set. `finish` (216–225) succeeds exactly at accepted_len=22. The exported
`queries_from_pairs` (305–320) chooses the advance at the first block whose
scan returns true, or advance[7] if no block returns true. If the 22nd fresh
word is draw `t`, its zero-based stop index is `min(t / 8, 7)` (integer
division): draw 23 selects index 2, draw 24 selects index 3, draw 64 selects
index 7. Success at draw 24/32/40/48/56 consumes the following block without
using a word. Failure consumes all 64 words and uses no successful output.

`crates/aspis-r1-cost-probe/src/transcript.rs:35–54` absorbs once, materializes
all eight squeeze/advance pairs, calls that shared decoder, maps failure to
`Error::Transcript`, and only on success installs the selected state (:55).
There is no sort. `verifier.rs:83–88` stores the returned array in Prepared;
checkpoint serialization (:333) iterates it in array order; resume validates
range/uniqueness (:352–359) without reordering. The admitted split is the
first ten queries then the remaining twelve; `Accumulator.next` and rho
powers follow that order, not index magnitude (`candidate.rs:213–214,245,296–305`). The existing stage-2 ordered
query-call proof and current S7 caller re-pin remain the consumers of this
order, not consequences of the new pure scan lemmas.

`QueryScanOrderedModel.successful_first22` proves the exact model output:
take the first 22 elements of the stable dedup fold over candidate words.
`successful_output` supplies length and Nodup; `blocks_flatten` proves that
early block stopping has the same accepted state as scanning the concatenated
words; `block_failure_smallRange` connects such a block failure to the event
used in the probability bound. These use the existing
`AspisV8R19.Q22WordScan.scan`, not a new replacement recurrence.

## Exact event and probability

Let N=262144, let W be uniform on `(Fin 64 → Fin N)`, and let E be that
scanning these words from `([],0)` fails to obtain 22 distinct indices.
`QueryScanModelFailure.failureProbability N` is exactly this event's
cardinality divided by `N^64`. `failure_smallRange` proves E implies
`card(range W) ≤ 21`. A normal one-collision birthday bound would be far too
weak; at least 43 repeats are required here.

For arbitrary n,k and N>0, every word string with at most k distinct values
factors as a table `(Fin k → Fin N)` composed with labels `(Fin n → Fin k)`.
`QueryScanExhaustion.factorization` constructs this factorization;
`smallRange_count` proves the count is at most `N^k k^n` by injection into
chosen factorizations. No large Finset is enumerated. Thus

```
Pr[E] ≤ N^21 · 21^64 / N^64
      ≤ 2^(18·21 + 5·64) / 2^(18·64)
       = 2^-454 < 2^-100.
```

The powers are manipulated symbolically in Lean. The bound is unconditional
in the independent-word model; there is no division by success probability.
`exhaustion_le_two_neg_100` also checks the requested weaker inequality.
The block result does not depend on the independent advance blocks.

For reference, the **exact** occupancy probability is
`sum(j=1..21, fallingFactorial(N,j) * StirlingSecond(64,j)) / N^64`.
The committed independent Python calculation gives
`2.972363022279527023888334031172256453743e-169`, about `2^-559.8342377`;
`evidence/queryscan-20261020/exact-probability.json` contains the complete
reduced numerator and denominator. This exact recurrence calculation is
arithmetic evidence, not a Lean proof of the exact formula; the release
inequality is the proved `2^-454` bound. The recurrence uses
`C(n+1,j)=j*C(n,j)+(N-j+1)*C(n,j-1)`, C(0,0)=1, truncating only states
above 21, from which the count can never decrease back into the event.

Eight attempts have union-bound probability at most `8·2^-454 = 2^-451`.
No independence between attempts is needed if each attempt's probability
bound holds for its reached history. The fixed 64-word law does not by
itself establish that conditional/adaptive premise in a shared ROM:
previous reads, repeated addresses and grinding must be handled by the
existing log/first-read/collision machinery. Never claim this bound for
arbitrary adversarially supplied blocks; all-zero blocks exhaust certainly.

## Where the abort charges enter

The actual prover calls `t.queries(31,&fbytes)?` at
`crates/aspis-r1-cost-probe/src/prover.rs:233`; the simulator does the same
at `sim.rs:174`. `Error::Transcript` propagates out of the attempt.
`prove_masked_retrying_with` (:361–362) retries only `Error::Rejected`;
a query error aborts the **entire invocation**, rather than consuming one
failed attempt and continuing. This differs from the mask/pole rejections
settled by LOG D73.4/D74.1–2. No source change was made to retry behavior.

Introduce a named **QueryScanAbortCoupling** obligation at the source/game
handoff: the source and total-model experiments agree until the union of
query-exhaustion events, and that union has mass ≤ δquery. Its components
are source scan refinement, uniform fresh-word transport, address/history
accounting, and agreement of all published outputs off that event.
`QueryScanAbortAccounting.transfer`, `coupling`, and `union_bound` prove the
finite probability transfer rules from these explicit hypotheses. They do
not discharge that obligation for Rust or the lazy oracle.

* Soundness: the gap-map target and
  `RawChecksAdaptiveFailureNoModel.checked_acceptance_failure_bound_no_model`
  (`lean/RawChecksAdaptiveFailureNoModel.lean:34–74`) currently end at
  `kappa Q + N·B + 2^-126`. At the **source-to-model coupling composition**,
  append `+ δquery`, bounded by `A·2^-454` when at most A appropriately
  charged query scans are reached. A is a scan-attempt budget, not silently
  the theorem's decoded-start budget N. Keep Q and N unchanged. The bank
  abort `2^-126` and query abort are different events. For the stronger
  acceptance-preserving refinement, source exhaustion rejects and therefore
  contributes zero accepted failures (as the existing
  `R0C.V3.Q22.q22_bound` already treats sampler errors); then no query abort
  charge is necessary. The additive term is a conservative coupling charge,
  not a newly discovered accepting attack or a reason to alter model M9.
* Privacy: add QueryScanAbortCoupling beside `RAddrIn`, `RCausal`, `RExh`,
  `ROpen` and `RComLog` at the deployed-source wrapper for
  `R1Z.PrivacyR1PBin.privacy_R1_games'`
  (`docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1PBin.lean:54–82`).
  Its real-game error currently contains `εexhP` inside the parentheses
  `M²/2^255 + εexhP`. A source-real versus model-real coupling adds
  `δquery,real` there. If the source simulator also aborts differently,
  compose its coupling too and add `δquery,sim` to the ideal side/overall
  advantage. Without a common coupled bad-event proof use their **sum**,
  not one charge for two independently bounded couplings. Each is at most
  `8·2^-454` under its corresponding history law. The published binary root
  `R1Z.PrivacySimulatorBin.privacy_R1_eff_binary` (:20–60) then has the
  conservative source-wrapper error
  `2^-109 + 2^-137 + δquery,real + δquery,sim`; with both eight-attempt
  premises this is at most `2^-109 + 2^-137 + 2^-450`.

These are exact insertion interfaces and proved generic transfer lemmas;
the existing soundness/privacy theorems were not edited or re-proved with
new source hypotheses. The model's `R1Wire.kstarOf` is an arbitrary total
field (`GamesR1.lean:82`); totality alone neither supplies the scanner nor
bounds exhaustion. On E its value may be arbitrary; off E the source
mapping must identify it with the selected advance index above.

## Pinned-boundary obstruction and next source obligations

`QueryScanPinnedBoundary` imports the actual
`ExtractedOpeningQueriesModel`, whose `QueriesModel.Boundaries` at
`lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean:22`
has only `decode` and `embed`. The checked `duplicate_output_possible`
constructs a boundary returning the zero-filled 22-array successfully on
any blocks. `selected_state_unconstrained` returns any supplied state.
These are countermodels to an unrestricted theorem over B, **not**
counterexamples to the Rust scanner. Accordingly the unrestricted pinned
boundary item is stopped, as required by the binding common rule 4.
`ExtractedPreparedReachability.prepare_success` cannot remove this boundary
by control-flow inversion alone.

The strongest retained positive endpoint is
`Query31ConcreteMaterializedScheduleFull.successful_default_concrete_materialized_query_schedule`
in `lean-candidates/query31-materialized-accepted-output-20261020/sources/`.
It ties eight materialized source digest pairs, the concrete byte decoder,
the Q22 chain, the returned query buffer, and the selected advance together.
Its `concreteBoundaries` uses a **candidate source-shaped driver**;
its README explicitly leaves production driver equality/adoption and Rust
array iterator/from_fn/map/default semantics open. This packet reuses that
result as prior evidence, not as a fresh compile or a production theorem.
The older actual-scan endpoint is at
`lean-candidates/current-query-scanner-20261019/QueryScanActualScanBridge-v3.lean`;
it also does not establish the original outer eight-block wrapper.

The exact remaining source handoff is:

1. Prove the production `queries_from_pairs` loop equal to the candidate
   first-stop driver, without changing/adopting verifier source. Its
   loop invariant must retain accepted buffer, accepted_len, draws, current
   block index, and selected advance; preserving only the final set loses
   verifier rho-power ordering.
2. Supply concrete std-library operation correspondence for array IntoIter,
   from_fn, map and Default. The pinned extraction's external signatures
   do not contain unsafe IntoIter/MaybeUninit implementation bodies. The
   prior `query31-axiom-free-scan-loop-20261020/source-snapshot/iterator-boundary.md`
   records the exact library source hashes and remaining invariant. Treat
   these as named hypotheses until proved, not new axioms or silent aliases.
3. Replace the reached `B.decode` in pinned queries/Prepared with that
   concrete operation and compose the same digest-pair schedule and selected
   state into `RawSamplerSuffixCorrespondence.query_correspondence`, row 32
   rho, and the frozen S2 caller re-pin. S1 queries/rho remain rows 30/31.
4. Instantiate `R1Wire.dec`/`kstarOf`, word uniformity and source-game coupling
   under the common logged oracle, with R10/R19 accounting; then the proved
   model failure bound supplies the QueryScanAbortCoupling probability.

No claim is made that these steps require a verifier source change. No
unadopted refactor is substituted for the frozen source. R4/R18 remain
conditional/partial; D74.4's **model probability** item is discharged, while
its source/game and other Semantic-error obligations remain.

## Verification and evidence

The packet is `evidence/queryscan-20261020/manifest.json`. Each attempt
retains its command, source snapshot, complete Lean log, `/usr/bin/time -l`
output, exit code, wall time, peak RSS, swaps, revision and dependency hashes.
The five new modules have 29 theorem audits, all standard-only. One unchanged
pinned dependency was rebuilt into the private object directory because its
cached artifact was absent; its two definition audits are standard-only.
No shared objects or existing Lean modules were overwritten.

Two dependency-owner failures are retained: the first boundary attempt had
no `ExtractedOpeningQueriesModel.olean`; the first dependency rebuild selected
a circle overlay's incompatible `AspisR1PublicPreparation.Funs` lacking
`trace.value`. Selecting the retained preparation owner
`/tmp/root-finish-prefix-deps-20261018` fixed it, and the dependent boundary
module was then checked against the same owner. Failed elaboration logs may
show `sorryAx`; none is a passing receipt or included in the accepted target
list. Algebra/proof draft failures and superseded successful order drafts
are retained separately from the final target list.

Focused local Lean only: 4.32.0, `-j1 -M4400 -DElab.async=false`, serialized
with the shared mkdir lock and an executable-name `lean` process check.
No full manifest replay, Rust/SBF build, extraction, CU gate or deployment
was run: the frozen runtime source/artifacts did not change, and the new
claims are focused model/interface proofs.

Final focused results (all exit 0, zero swaps; peak RSS in bytes):

| Target | Attempt | Wall seconds | Peak RSS |
|---|---|---:|---:|
| QueryScanExhaustion | exhaustion-v3 | 10.91 | 2855714816 |
| QueryScanModelFailure | failure-v2 | 9.12 | 2867167232 |
| QueryScanOrderedModel | ordered-v4 | 11.66 | 2856009728 |
| QueryScanAbortAccounting | accounting-v1 | 5.98 | 2857189376 |
| QueryScanPinnedBoundary | boundary-v2 | 1.63 | 2240053248 |
| ExtractedOpeningQueriesModel (unchanged dependency) | boundary-dep-v2 | 7.08 | 2275835904 |
