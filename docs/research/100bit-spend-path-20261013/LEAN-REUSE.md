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
| Masked semantic sumcheck and extraction | Existing `R0P.Mask` and `R0P.SemD3Glue` | Available to reuse, but the complete R1 composition has not been checked. The old 32-round masked D3 theorem cannot be applied unchanged to the new 33-round schedule. |

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

The old masked semantic algebra is substantial reusable work. Its application
still requires exact point and Libra construction/embedding, BaseTyped and
public-input premises, the accepted masked sumcheck equations, and the
correct early/eta/alpha bad-event exclusions for the new transcript. The
source-only inventory is `SEMANTIC-TERMINAL-INVENTORY.md`.

The new `SamplerWord` and `SamplerWordPass` proofs connect actual Lean
UInt64 shift/or/div/mod and UInt32 casts to the previously checked Nat/list
arithmetic. They do not claim Rust refinement. Byte order, array traversal,
repeated division, carry branches, and field construction are inventoried in
`SAMPLER-SOURCE-INVENTORY.md`.

The shared-oracle Fiat–Shamir instantiation, complete source correspondence,
universal masking/simulator argument, and final private-spend security claim
remain open. No grinding or work-normalization credit is added by this reuse.

## Checked reuse checkpoint

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

Further existing sampler components are available: `R0C.ModuloField` proves
the little-endian 32-byte rank and constructs the eight-digit WideExact
bijection; `AspisV8R19.SamplerWordBridge.source_word` proves an extracted
four-byte read equals the retained integer word model. These are reuse
candidates for the remaining byte/field connections, not newly discharged
Rust-refinement obligations.
