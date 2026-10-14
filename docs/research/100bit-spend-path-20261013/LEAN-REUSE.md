# Reusing the existing Lean development

The R1 path reuses the expensive decoder, list, and sampling results. The new
work is chiefly a set of explicit bridges. A theorem for the old protocol does
not automatically become a theorem for the new verifier: its premises, index
order, field embeddings, and transcript schedule must be discharged again.

The latest [conditional Fiat–Shamir theorem](UNIFIED-FIAT-SHAMIR.md) reuses
the existing v3 security theorem with one decoder covering all 33 rounds.
Global dispatch, actual-experiment injection, and the adaptive decoder-density
connection are now checked. The bound retains `Qtot * maxErr + 3*Qtot²/2²⁵⁶`.
The concrete extractor/decision/classifier and D1/D2/D3 numerical instance,
source correspondence, and complete privacy remain open.

The old existential extractors also need care: the inspected R0FS/R0C
definitions choose a witness if one exists and ignore the oracle table.
Their reuse does not establish efficient knowledge extraction for a spend.
The new conditional theorem leaves the extractor explicit, and that security
obligation remains open.

Two further checked connections reuse the field and counting development:
[whole-word dual-pad correction](DUAL-PAD-WORD-BRIDGE.md) lifts the quadratic
identity to legal pad-space repairs with zero raw observations, given
explicit eligible noise preimages; [opening sampler bounds](OPENING-SAMPLER-BOUNDS.md)
apply the old modulo-counting theorem to all four WideExact opening bad sets.
The corrected gamma adapter uses modulo `P^8-1` and excludes zero. Their
combined fourteen-audit checkpoint is green. Universal mask ranks and the
adaptive source/protocol instantiation remain open.

The [knowledge and oracle boundary](KNOWLEDGE-AND-ORACLE-BOUNDARY.md)
records why an existence extractor, bounded mathematical decoder, and
Merkle path-binding theorem are separate ingredients. It also identifies
terminal hash reads missing from the current Boolean-decision verifier.
The [new oracle/Merkle checkpoint](ORACLE-MERKLE-REUSE.md) supplies a generic
terminal-oracle verifier interface and adapts the old path/leaf proof to
32-byte hashes and R1's three salted leaf layouts. Connecting those results
to the unified security theorem and source is still required.

[Finite-table Merkle recovery](MERKLE-TABLE-RECOVERY.md) now gives a
constructive lookup and an exact recovery/collision/missing-preimage
alternative, plus literal oracle-program trace equations. A symbolic
target-parser union bound and the old joint-list bound for partial lanes
are also checked. The accompanying D2 interface audit prevents treating
an arbitrary-table existence reduction as a completed knowledge proof.

The [recorded byte-log connection](MERKLE-RECORDED-LOG.md) now applies that
recovery theorem to strict node/leaf parsers, proving that missing preimages
are absent from the supplied query log. It also reuses the old first-read
calculus to cover later hits on earlier parsed child targets. The supplied
root case and canonical bounded-address/byte-log correspondence were explicit
obligations at that checkpoint, which has 29 standard-only axiom reports.
The [canonical recovery connection](CANONICAL-MERKLE-RECOVERY.md) now derives
byte-log consistency by filtering only the recovery records, reuses evaluator
renaming for the literal opening program, and covers the initial-C1 root case
using the existing public-initializer parser. Its 27-audit checkpoint is green.
The full trace and query budget retain every adversarial read. C2/folded roots,
commitment-time prefix selection, source correspondence, and complete knowledge
security remain open.

The [unified sampler connection](UNIFIED-SAMPLER-BRIDGE.md) puts initialization,
the domain-transition hash, q22, and rho into one schedule. The
[trace-recovery connection](UNIFIED-TRACE-RECOVERY.md) handles the row after q22;
the [semantic cases](UNIFIED-SEMANTIC-DECODER.md) and
[reseed/opening cases](UNIFIED-RESEED-OPENING.md) cover the middle rounds.
These bridges apply existing proofs without changing the old theorem statements.
Source/account correspondence and complete privacy remain separate obligations.

| Existing result | Reuse in R1 | Scope of the checked result |
|---|---|---|
| Exact initial decoder/agreement and width-29 correlated agreement | `InitialResponses`, `TwoFoldExtraction`, `ConcreteBinding` | The existing initial thresholds and challenge cap are retained. |
| Exact 256-coefficient degree-three matched-response theorem | `SecondFoldMatched`, `SecondFoldRestoration` | A fourfold repeated lift reuses the theorem for the 256-to-64 fold; both folds then recover one tuple in the literal joint list. |
| Joint committed-word list bound of 100 | `JointList`, `InitialResponses`, `ConcreteBinding` | Functional and round comparisons union over that same list; candidate uniqueness is not assumed. |
| Stopped, bounded 22-query sampling law | `BoundedQueries`, `RawQueryBound`, unified query decoder | The independent-answer law includes exhaustion. The actual shared-oracle decoder now connects to the generic FS theorem; concrete D2 remains open. |
| Existing v3 Fiat–Shamir theorem | `UnifiedInj`, `UnifiedChainDensity`, `UnifiedFiatShamir` | The unified transcript satisfies the decoder interfaces and gives a conditional bound with D1/D2/D3 explicit. |
| Four codeword/message subfield-descent theorems | `Wide/SubfieldDescentCore`, `CandidateDescent` | Every candidate in the literal R1 list has the required lane field types when the committed words are typed. |
| Original R0 Boolean weights and coefficient reindexing | `R0/OpeningWeights`, `D18OpeningWeights`, `SemanticOpening` | The D18 point rows give exactly the older transported point functionals; the derived candidate satisfies the point/extra/codeword-typing interface. |
| Masked semantic sumcheck and extraction | `SemanticTransport`, `MaskedSemantic` apply existing `R0P.Mask` and extraction theorems | The deterministic R1 candidate-to-input-note connection is checked, with explicit bad-event exclusions. The old 32-round masked D3 theorem cannot be applied unchanged to the new 33-round schedule. |
| Production value rows, copy registry, Poseidon/schedule/asset/digest gates | `SpendValues`, `OutputCopyLinks`, `OutputNotes`, `SpendExtraction` | The actual R1 candidate now gives bounded integer conservation and recipient/change note bindings, with explicit variant/public-option guards. Append correctness remains separate. |

## Actual experiment trace recovery

The [new trace connection](UNIFIED-TRACE-RECOVERY.md) reuses the old verifier
read-inclusion and evaluator-consistency theorems, prefix/query recovery, and
background trace-following machinery. It supplies their phase and read facts
from the unified run, including earlier prover queries. The guarded row-32
decoder now returns the literal prefix/message/challenge on that experiment
trace under the explicit codec, query-budget, and collision premises. The later
case bridges now cover the other rounds. The later conditional FS theorem
composes their global dispatch and injection; the concrete security/privacy
conclusions remain open.

## New typed-candidate connection

`CandidateDescent.candidate_codeword_typed` starts from the actual R1 list
membership, which gives at least 38,230 simultaneous agreement positions.
For each lane this exceeds the existing 1,024-position decoder overlap cap.
It applies the existing Galois-descent theorem to that support and then applies
the existing message-descent theorem. Candidate field membership is therefore
a conclusion, not an extra assumption about a recovered witness.

`large_matching_implies_typed_claims` composes this with the existing R1
opening theorem. It retains the latter's explicit good-challenge exclusions,
accepted pairing equations, and matching-support premise. The committed-word
typing premise still needs source/parser correspondence.

`SemanticOpening.large_matching_implies_witness` instantiates the seven rows
in verifier order: inactive, three D18 point rows, extra, and two circle rows.
It derives the older point/extra/codeword-typing witness shape, using the
exact moved `AspisR0.Opening` weight definitions. Its extra and circle rows
remain explicit inputs, and its model is E-valued. It is not yet an equality
to the Rust K-valued constructors followed by their field embedding, a parser
theorem, or the final semantic spend theorem.

## Reuse without weakening the old results

The three generic theorems formerly in `Wide/SubfieldDescent.lean` and the
message theorem formerly in `R0P/MessageDescent.lean` were moved to
`Wide/SubfieldDescentCore.lean`. All four statements and proof bodies match
the originals byte-for-byte. Their original modules now import the shared
core; the concrete WideExact specialization remains in its original module.

The `eqWeight`, `indicator`, `coeffWeight` definitions and five associated
reindexing identities were moved unchanged out of `R0/OpeningDefinitions`
into `R0/OpeningWeights`. `RoundNormalization.dot` was similarly moved to a
small module. This avoids loading an entire old opening protocol simply to
reuse its weight definitions. The declaration names and original contexts
are preserved. The earlier D18 draft was uncompiled; its checked replacement
uses the original finite-field context and fixes the inverse-permutation
proof orientation.

The narrow field module `ExactTowerBase` is also reused. `ExactTowerFinite`
adds only product-cardinality proofs and finite instances, so `WideTower`
can use the same quadratic field construction without importing the legacy
sampler/hiding development. The cached decoder interfaces also retain a
Mathlib Fin enumeration; that dependency is made explicit in the cardinality
module rather than restored through the entire legacy tower import chain.

## What remains

The field-level semantic connection is now checked. `SemanticTransport`
identifies the actual three semantic point functions and the Libra row,
and derives `BaseTyped` from the recovered candidate's descent.
`MaskedSemantic.large_matching_extracts` applies the existing concrete
mask-degree, masked sumcheck, eta, zerocheck, lane, LogUp, and extraction
results to that candidate. Its conclusion retains literal R1 list membership,
production constraints, copy balance, and `InputNoteExtracted`.

Source construction/embedding, public-input and committed-word typing,
accepted parsed checks, and the early/eta/alpha exclusions with the new
transcript's timing still need correspondence and probability arguments.
The newer spend-note checkpoint adds bounded integer balance and output-note
bindings to that relation, while full settlement and privacy remain open. See
[`SPEND-NOTE-BRIDGE.md`](SPEND-NOTE-BRIDGE.md) and
[`MASKED-SEMANTIC-BRIDGE.md`](MASKED-SEMANTIC-BRIDGE.md).

The new `SamplerWord` and `SamplerWordPass` proofs connect actual Lean
UInt64 shift/or/div/mod and UInt32 casts to the previously checked Nat/list
arithmetic. They do not claim Rust refinement. Byte order, array traversal,
repeated division, carry branches, and field construction are inventoried in
`SAMPLER-SOURCE-INVENTORY.md`.

`SamplerByteWord` now applies the existing extracted `source_word` and
array round-trip theorems to one actual four-byte read. `SamplerBytePass`
composes those reads, in reversed eight-word order, with the checked machine
division pass. The remaining 32-byte rank identity and mutable/repeated
sampler execution are not asserted by these theorems.

The generic shared-oracle Fiat–Shamir connection is now checked. Its concrete
D1/D2/D3 and numerical instance, complete source correspondence, universal
masking/simulator argument, and final private-spend security claim remain
open. No grinding or work-normalization credit is added by this reuse.

## Earlier checked reuse checkpoint

The final combined import/axioms target `R1ReuseCheckpoint` passed on the NUC
in 1.35 s with peak RSS 3,501,880 KiB and zero swap, in its own 4G/6G/0-swap
scope. Its twelve axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The per-target manifest and compiled-object archive are in
`evidence/lean-reuse-checkpoint-20261013/`.

The narrower imports exposed cached declarations that had selected a prime
instance from the old representation module. The affected polynomial-pair,
chord, matched-instance and list modules were rebuilt in dependency order;
the old opening definitions now compile in 1.70 s at 3,519,608 KiB. One
historical `rfl` in `ChordImage.pairWord_zero` exceeded recursion depth even
at 4096. Its unchanged statement is now proved using the already existing
`storedInitialCirclePoint20_child_zero` lemma, avoiding reduction of the
stored domain construction. The failed attempt and its symbolic replacement
are retained in `evidence/lean-r0-primefact-replay-20261013/`.

This is a focused component checkpoint using the pinned compiled cache, not
a from-scratch replay of the entire historical release manifest. The final
semantic/source/Fiat–Shamir/privacy conclusions above remain open.

## Semantic and byte-sampler checkpoint

`R1SemanticReuseCheckpoint` imports both new connections and passed on the
NUC in 1.65 s, with peak RSS 4,041,956 KiB and zero swap in its own
4G/6G/0-swap scope. All six combined axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`. The final semantic theorem itself
passed in 1.63 s at 3,587,236 KiB. Evidence is retained in
`evidence/lean-masked-semantic-20261013/`; the lower import refresh and
four-byte bridge have separate evidence directories.

The import refresh retains the old theorems. `ModuloField` now explicitly
imports `CircleGroupOrder`; three old R0P modules refer to the same extracted
tower via `ExactTowerBase` instead of the old namespace. All other changes
to the historical dependency chain are compiled-object refreshes. The
old D3 and density results were rebuilt as dependencies, not applied as
an R1 Fiat–Shamir theorem.

The newer `R0Z.PureRounds` branch also contains reusable closed forms and
sumcheck-chain identities. Its payload-dependent statements use the old
one-fold output, so they require a separate R1 correspondence; surjectivity
definitions are not proofs of the required mask rank. The pinned source-only
inventory is [`PURE-ROUND-REUSE.md`](PURE-ROUND-REUSE.md).

## Semantic prefix connection

The next checked bridge, `SemanticPrefix.large_matching_extracts_of_prefix`,
derives the candidate exclusions from the explicit semantic classifier at
each of the first 25 parsed rows, then applies the R1 opening and extraction
theorems. It reuses the old pre-C2 padding argument for lambda/chi, so it
does not assume H1/G was committed before those challenges. The literal R1
and R0 candidate lists are proved equivalent.

The existing per-prefix sampler bounds are retained. `SemanticBudget`
proves their 25-row sum is `303100 * (1+deltaQ)/P^4`; this accounting does
not supply the missing shared-oracle reduction. The combined checkpoint
passed on the NUC in 1.38 s at 3,566,892 KiB, with zero swap and standard
axioms only. See [`SEMANTIC-PREFIX-BRIDGE.md`](SEMANTIC-PREFIX-BRIDGE.md)
for the exact theorem inputs, timing argument, and remaining source,
Fiat–Shamir, full settlement, and privacy obligations.

## Spend-note connection

The production value and copy lemmas now prove three `<2^30` values and
integer conservation without the research-only positivity lane. The existing
Poseidon and schedule interfaces, with six named copy links and the asset
and digest equations, prove change-note extraction for both variants and
recipient-note extraction for private transfers with a present public
recipient. `SpendExtraction.large_matching_extracts` applies these results
to the same literal R1 candidate under unchanged opening/semantic premises.

The combined checkpoint passed in 1.40 s at 3,568,284 KiB peak RSS with zero
swap and eight standard-only axiom audits. No historical source or theorem
was modified. See [`SPEND-NOTE-BRIDGE.md`](SPEND-NOTE-BRIDGE.md) for exact
scope and receipts. The source-only inventories
[`APPEND-REUSE-NEXT.md`](APPEND-REUSE-NEXT.md) and
[`FS-REUSE-NEXT.md`](FS-REUSE-NEXT.md) distinguish reusable generic results
from the current append-gate and 33-round protocol obligations still open.

## Literal append connection

The next bridge reuses the old pair-occupancy theorem and existing
schedule/Poseidon interfaces to derive the ordered output pair, twenty
append nodes, next root, and carry frontier entry from the production
gates. A separately named non-carry public-check premise supplies the
remaining frontier cells. It strengthens the same extracted R1 candidate.

The combined checkpoint passed in 1.37 s at 3,570,308 KiB peak RSS with
zero swap and twelve standard-only axiom audits. The only historical
source change narrows an import in `V7PairLeafOccupancy`; its theorem
statements and proof bodies are unchanged. See
[APPEND-GATE-BRIDGE.md](APPEND-GATE-BRIDGE.md). The frozen-table recurrence,
chronological tree correspondence including the final full-capacity
insertion, Rust refinement, shared-oracle law, and privacy remain open.

## Concrete table and chronological root connection

The later [tree bridge](APPEND-TREE-BRIDGE.md) closes the frozen-table
recurrence and chronological-root correspondence in the field model. It
reuses the old round-split certificate pattern and the existing generic
append/reconstruction theorems for both ordinary and full-capacity carries.
The same R1 candidate now has the correct root for old leaves plus its
ordered output pair, given the authenticated old-frontier invariant.

All 53 final focused targets passed. The combined checkpoint took 1.39 s
at 3,590,024 KiB with zero swap and ten standard-only axiom audits. Stored
frontier preservation, actual source/account correspondence, shared-oracle
soundness, and privacy remain separate obligations.

## Saved frontier and invariant continuation

The [state bridge](APPEND-STATE-BRIDGE.md) now identifies the literal saved
frontier with the existing generic carry result, using symbolic bit and list
proofs. It reuses `FrontierInvariant.append_preserves`,
`append_terminal_correct`, and `genesis_invariant`. The same R1 candidate
therefore carries the chronological root, canonical inactive cells, and the
post-append frontier invariant. The final insertion gets the full-root and
empty-frontier result, without claiming that a full tree can be appended to.

Initialization and continuation are proved in the model under the explicit
index/frontier read-write link. Eight focused targets passed, including the
combined checkpoint: 1.47 s, 3,591,216 KiB, zero swap, thirteen standard-only
axiom reports. Rust/account enforcement of the link and guards, the complete
input-pair membership semantics, shared-oracle soundness, and privacy remain
open. No historical theorem statement or proof body was changed in this step.

## Input-pair selection connection

The [input-pair bridge](INPUT-PAIR-BRIDGE.md) reuses the old pair-occupancy
model, path constraints, and copy/Poseidon interfaces. Two literal copy
records connect the input pair's second commitment and selected side bit.
The same R1 candidate now has a valid input pair, an occupied selected slot,
and a selected commitment equal to the input-note hash block's output.

Five focused targets passed, including a 1.39 s combined checkpoint at
3,592,484 KiB, zero swap, and nine standard-only axiom audits. Connecting
these literal trace facts to one concrete secret/nullifier/forest witness
remains the next semantic step. The source, shared-oracle, and privacy
obligations remain open.

## One concrete input relation

The [input-witness bridge](INPUT-WITNESS-BRIDGE.md) now exposes the old
extraction proof's actual secret, salt and path, and joins them to the same
candidate's occupied input pair. Its other commitment is proved to be the
first path sibling; the first path step hashes that exact ordered pair.
The old bounded-value theorem gives the input value and integer conservation.

Five focused NUC targets passed on their first attempt, including a 1.51 s
checkpoint at 3,591,584 KiB, zero swap and six standard-only axiom reports.
Existing historical declarations are byte-identical. Authorization of the
public anchor from account state, Rust refinement, the 33-row shared-oracle
instantiation and privacy remain open.

## Reuse toward the actual R1 Fiat–Shamir schedule

The [transcript adaptation audit](FS-R1-ADAPTATION.md) identifies why the
old 32-row theorem cannot simply be renamed: R1 has a q22 round followed
by rho, q22 can select an earlier continuation state, later extra claims
arrive in row 25, and there is a domain-transition hash before opening.

Six focused targets now reuse the old semantic classifier and no-hit
characterization, q22 scan definition, and no-collision table lemmas.
They prove invariance of the early semantic checks under replacing the
extra vector and recovery of the predecessor path for the actual selected
query state. The 1.37 s combined checkpoint used 3,557,136 KiB, zero swap,
and reported ten standard-only axiom audits. The full new decoder, its
completion law, D1/D2/D3 instance, source correspondence and privacy remain
open; these structural results do not close those obligations.

## Query recovery before rho's first read

The [first-read bridge](QUERY-FIRST-READ-BRIDGE.md) extends the old
no-collision, first-read order, and q22 scan lemmas. It derives the selected
advance prefix from the table before the following endpoint, discovers the
query absorb boundary, and reconstructs the exact query result by completing
only missing squeeze answers. It does not assume the unused advance tail
is already in that table.

Twelve focused targets passed. The final combined checkpoint took 0.74 s
at 1,828,696 KiB, zero swap, with 28 standard-only axiom reports. The new
finite-missing-list wrapper is suitable for the existing list-based
completion interface; this deterministic equality does not establish that
interface's probability law or injection for the full R1 transcript.

## Reusing the completion-sampler law

The [completion-law bridge](QUERY-COMPLETION-LAW.md) now reuses the old
`DQ.accFrom_map`, `BSOk.blaw_split`, `pmean_le`, and duplex `samp_mean`
theorems. The recovered q22 component accepts the same positional answer
list as the old decoder. Its actual oracle-answer list recovers the
actual result, and the following single-round independent-answer law
separates exactly into an outer background mean and the old fresh sampler
law. The fixed-completion bound remains explicit.

Six focused final targets passed, with a 1.36 s combined checkpoint at
3,518,516 KiB, zero swap, and twelve standard-only axiom reports. The
trace-following/injection connection and the complete R1 prefix, hash-edge
and D1/D2/D3 instance remain open.

## Actual trace following and local adaptive rho bound

The [trace bridge](QUERY-TRACE-BRIDGE.md) now derives the selected missing
list's freshness, disjointness and suffix reads, then reuses `bfollow_ok`
to recover the actual query and following challenge. Its local decoder
gets the predecessor state from the queried address. `chainB` and the
existing 21-root and accepted-query results give a local adaptive accepted-
miss bound below `2^-119`, under explicit modulo-sampler and fixed-data
premises. This is the final batching term, not the full spend's security.

Ten focused targets passed. The combined checkpoint took 1.36 s at
3,525,648 KiB, zero swap, with eighteen standard-only axiom reports.
Earlier records, hash transitions, the full R1 instance, source refinement
and privacy remain open.

## Opening-domain hash connection

The [reseed edge bridge](RESEED-EDGE-BRIDGE.md) preserves the source's P3
domain hash and models it at the end of row 26. It reuses the old table
uniqueness, first-read bound, trace-following and sampler-law machinery.
An added parsed-state event accounts for the trailing-state frame; the
combined collision bound is `3 * Qtot^2 / 2^256`. Recovery before the next
absorb, the literal P3 frame, and the local reseeded sampler now compile.

The combined checkpoint passed in 1.42 s at 3,526,844 KiB, zero swap, with
25 standard-only axiom reports. Initialization, strict full-prefix parsing,
the full FS/source instance and privacy remain open. The local recovery
function is not itself a strict domain validator.

## Initial public/commitment hash and strict prefix recovery

The [initial-edge bridge](INITIAL-EDGE-BRIDGE.md) now models initialization as
an actual hash query and proves a strict public-prefix/C1 parser. The old
`bfollow_ok` theorem and independent sampler law recover the actual row-zero
challenge and state. A backward decoder reuses output uniqueness and
advance-predecessor recovery to return the earlier ordinary records and C1
from the table before the next absorb. The table cells and lookup success
are derived from trace facts. The strict opening-domain parser also closes
the local validation duty described in the preceding checkpoint.

Fifteen final targets passed on the capped NUC. The combined checkpoint took
1.41 s at 3,529,016 KiB, zero swap, with 33 standard-only axiom reports.
Typed row validation, complete missing-answer and reseed/query composition,
the full FS/source instance, account correspondence and privacy remain open.

## Recovery across the domain transition and challenge completion

The [opening-prefix bridge](OPENING-PREFIX-BRIDGE.md) now derives the semantic
and ordinary-opening record lists from the table before the next absorb,
including strict recovery of both special hash edges. It carries the reseed
output at the end of the last semantic round while preserving that round's
message and squeeze state. The indexed abstract message decoder, the older
`completeRounds` function and `DQ.accFrom_map` recover the actual challenges
from the computed missing-answer list. The older background-mean split and
ordinary sampler law apply to every fixed prefix completion.

Fifteen focused targets passed. The combined checkpoint took 1.38 s at
3,530,180 KiB, zero swap, with 38 standard-only axiom reports. The complete
adaptive trace-following and q22/rho composition, concrete message/source
instance, account/settlement correspondence and privacy remain open.


## Endpoint cases and early-prefix recovery

[UNIFIED-ENDPOINTS.md](UNIFIED-ENDPOINTS.md) connects the initial and rho
decoders to the exact `FS2.Protocol` first-cell/output interface on the actual
experiment. The initial sampler law reuses the existing initial-law proof.
The two recovery collision events now have one checked union bound of
`3 * Qtot^2 / 2^256`. A typed-prefix theorem derives the earlier records
before every row 1 through 26 from the actual reads and transitions.

Completing and dispatching the middle-round decoders, all of `Inj3`, the
full D1/D2/D3 and numerical instance, source correspondence and privacy
remain open. No old theorem statement or proof body is changed here.


## Completing semantic rows 1–25 with existing proofs

[UNIFIED-SEMANTIC-DECODER.md](UNIFIED-SEMANTIC-DECODER.md) gives one generic
address/table decoder case for all 25 ordinary semantic rounds. The actual
experiment theorem derives typed prefix recovery, known cells, missing-answer
freshness and trace following, then returns the exact protocol triple.
It reuses the existing prefix table, backward walk, completion, sampler-law
and evaluator proofs without altering their statements or bodies.

The completing sampler law and bound transfer retain an explicit fixed-prefix
bound. Reseed/opening/query cases, correct global dispatch, the full generic
security instance, source correspondence and privacy remain open. The combined
NUC checkpoint passed with fifteen standard-only axiom reports; exact attempts
and source/object hashes are preserved in its evidence bundle.


## Reseed and ordinary opening cases

[UNIFIED-RESEED-OPENING.md](UNIFIED-RESEED-OPENING.md) connects row 26 and
rows 27–30 to the actual experiment using the existing reseed sampler,
opening-prefix walk, table-cell and completion proofs. The extra P3 hash
remains in row 26's next state. Prefix recovery and known-cell/read facts
also hold before query row 31, while that row's completing decoder remains
separate.

The new sampler-law and bound-transfer theorems keep their fixed-prefix bounds
explicit. Query-case completion, correct global dispatch, the full generic
security and numerical instance, source correspondence and privacy remain
open. Sixteen focused targets passed on the NUC; the final combined checkpoint
has 24 standard-only axiom reports and recorded source/object/resource evidence.


## Query case and shared decoder representation

[UNIFIED-QUERY-DECODER.md](UNIFIED-QUERY-DECODER.md) connects query row 31 to
the actual experiment. The background sampler lets squeeze reads arrive in
arbitrary order relative to their same-step advances, retains the advance
list, and uses the existing bounded scan's exact output. The law transfer
keeps the fixed-prefix bound explicit. Generic singleton-result adapters
preserve the existing state-valued decoders' follow and law behavior.

Fourteen final targets passed on the capped NUC. The combined checkpoint has
39 standard-only or empty axiom reports. Symbolic label injectivity and
initialization/absorb separation are checked prerequisites for the next
combined dispatcher; that dispatcher and the full security, source, and
privacy results remain open.

## Three commitment roots and finite-table recovery

[THREE-COMMITMENT-RECOVERY.md](THREE-COMMITMENT-RECOVERY.md) reuses the
canonical byte log, literal Merkle program, finite lookup, parsed first-hit
events, and duplex collision theorem for C1, C2, and the folded root. Eight
new components and their combined checkpoint passed; the checkpoint has
28 standard-only axiom reports. Commitment-time prefix selection and the
actual full trace, efficient extraction, source correspondence, and the
complete security/privacy instantiation remain separate obligations.
