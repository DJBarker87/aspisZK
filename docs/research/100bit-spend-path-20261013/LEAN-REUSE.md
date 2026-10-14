# Reusing the existing Lean development

The R1 path reuses the expensive decoder, list, and sampling results. The new
work is chiefly a set of explicit bridges. A theorem for the old protocol does
not automatically become a theorem for the new verifier: its premises, index
order, field embeddings, and transcript schedule must be discharged again.

| Existing result | Reuse in R1 | Scope of the checked result |
|---|---|---|
| Exact initial decoder/agreement and width-29 correlated agreement | `InitialResponses`, `TwoFoldExtraction`, `ConcreteBinding` | The existing initial thresholds and challenge cap are retained. |
| Exact 256-coefficient degree-three matched-response theorem | `SecondFoldMatched`, `SecondFoldRestoration` | A fourfold repeated lift reuses the theorem for the 256-to-64 fold; both folds then recover one tuple in the literal joint list. |
| Joint committed-word list bound of 100 | `JointList`, `InitialResponses`, `ConcreteBinding` | Functional and round comparisons union over that same list; candidate uniqueness is not assumed. |
| Stopped, bounded 22-query sampling law | `BoundedQueries`, `RawQueryBound` | The checked independent-answer law includes sampler exhaustion; it is not yet the new shared-oracle Fiat–Shamir instantiation. |
| Four codeword/message subfield-descent theorems | `Wide/SubfieldDescentCore`, `CandidateDescent` | Every candidate in the literal R1 list has the required lane field types when the committed words are typed. |
| Original R0 Boolean weights and coefficient reindexing | `R0/OpeningWeights`, `D18OpeningWeights`, `SemanticOpening` | The D18 point rows give exactly the older transported point functionals; the derived candidate satisfies the point/extra/codeword-typing interface. |
| Masked semantic sumcheck and extraction | `SemanticTransport`, `MaskedSemantic` apply existing `R0P.Mask` and extraction theorems | The deterministic R1 candidate-to-input-note connection is checked, with explicit bad-event exclusions. The old 32-round masked D3 theorem cannot be applied unchanged to the new 33-round schedule. |
| Production value rows, copy registry, Poseidon/schedule/asset/digest gates | `SpendValues`, `OutputCopyLinks`, `OutputNotes`, `SpendExtraction` | The actual R1 candidate now gives bounded integer conservation and recipient/change note bindings, with explicit variant/public-option guards. Append correctness remains separate. |

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

The shared-oracle Fiat–Shamir instantiation, complete source correspondence,
universal masking/simulator argument, and final private-spend security claim
remain open. No grinding or work-normalization credit is added by this reuse.

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
