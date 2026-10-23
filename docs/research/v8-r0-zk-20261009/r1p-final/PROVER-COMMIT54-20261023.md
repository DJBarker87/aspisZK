# Part 54: owned simulator encoder

Target not yet established. Branch `codex/cx-prover-commit54-20261023`.
Allocated attempts J10600–J10699 only. No shipped source is changed.

## Endpoint before/after

Verbatim endpoint modules are retained in `endpoint/before.lean.txt` and
`endpoint/after.lean.txt` under the part-54 evidence directory. Both currently
retain the deployed RustProverRefinement premise. No payload equality is claimed.

## Stage 1: explicit encoder owner

The owner uses an explicit finite recursive strided collector and a finite-height
evaluator. Four channel vectors are built without iterator adapters. Extraction,
source binding, native equivalence and model induction are separate obligations.

Charon/Aeneas succeed (1.458/0.476 s, 210996/71280 KiB, zero swap).
J10603 checks the exact extracted declarations after byte-identical arithmetic
rebinding. J10608 proves the complete strided collector output, including every
read index, output ordering, finite termination, and release wrapping bounds.
It exits 0, 2.53 s, 4118444 KiB, zero swap; all four printed axioms are standard.

J10600 exposes missing Lean 4.32 core companion artifacts. J10601 is refused
without a compiler invocation. The cache completion adds read-only links, and
the dependency fingerprint now records the actual split core artifacts. J10602
exposes two omitted conversion imports, repaired by reusing byte-identical
Samples49 declarations. J10604–07 are rejected collector proof drafts; their
full diagnostics are retained. No cap or heartbeat limit is raised. Receipts
pin source revision and exact source/dependency hashes. The accepted source
has no proof holes. No shared object is overwritten.

## Stage 2: owned evaluator, channel array and fibre output

J10611 proves success, canonicality and the exact recursive polynomial value
for arbitrary canonical 2^h coefficients (h≤8), with both split vectors derived
from reads. J10614 composes all four 256-coefficient channels. J10615 checks
the newly extracted phi/wrapper; retained extracted callees are byte-equal.
J10616 proves the complete owned encode_with_nodes result at supplied canonical
nodes and fibre coordinates. J10617 proves symbolically that this recurrence,
at a repeated-doubling node sequence, equals the natural Chebyshev-product
basis sum. Node equality is not inferred from that generic identity.

Accepted Lean attempts (exit 0, zero swap, standard printed axioms only):

| Attempt | Exact module suffix | Wall s | Peak RSS KiB |
|---|---|---:|---:|
| J10611 | R1Z.ProverCommitEncoderEval54 | 2.96 | 4136436 |
| J10614 | R1Z.ProverCommitEncoderChannels54 | 1.96 | 4110920 |
| J10615 | AspisR1ProducerRelease47.EncoderLeaf54 | 1.09 | 2636620 |
| J10616 | R1Z.ProverCommitEncoderLeaf54 | 1.70 | 4100276 |
| J10617 | R1Z.ProverCommitEncoderMath54 | 1.86 | 4114712 |

J10609/10 are conversion/division drafts. J10612 exposes concrete array
reduction under change; J10613 proves all theorems but rejects a duplicate
local attribute. J10614 uses an opaque array and symbolic length lemma.
No limits are raised. The second extraction exits 0/0, 1.811/0.494 s,
210944/71808 KiB, zero swap.

Kani proves arbitrary current even, odd and channel iterator read contracts
(even-v2, odd-v2, channel-v2), then split/channel iteration comparisons
using stub_verified (split-v3 and channel-iteration-v3). Each contract has its
own successful proof_for_contract harness. This checks a single transition at
the selected remaining suffix; full native iterator-state/Vec composition is
not inferred. Values are unrestricted u32 cells, with no arithmetic
performed in the collector. Source spans and the projection boundary are
in native-source-pins.json.

The broad nth(k) diagnostic even-v1 was stopped at 6460452 KiB (142.114 s),
zero swap. It is replaced by a local transition contract rather than retried.
The split-v2 CLI preflight omitted Kani's stubbing feature and is rejected; v3
changes the feature set. Accepted native wall/RSS KiB: even-v2 6.252/496312;
odd-v2 7.174/583172; channel-v2 10.571/339116; split-v3 2.996/266596;
channel-iteration-v3 9.193/189240. All exit 0, zero swap, explicit opt-level=3,
6G/8G/zero-swap/64-task scope. Raw logs and input snapshots are retained.

The native caller instantiates encode_at at M31 and QM31, whereas the
current extracted owner is WideExact. Embedding those specializations, exact
nodes_for provenance, leaf assembly and semantic/opening caller remain
explicit. This stage does not establish native simulator payload equality.

## Stage 3: exact owned node geometry

The nodes owner extracts reversal, binary CM31 powering, repeated base-field
doubling, one aligned node and the nine-cell array. J10618 rejects the
backend's U8 shift operand; explicit Rust u32 shift casts repair the owner.
J10619 accepts the revised extraction. No generated code is patched.

J10622 proves arbitrary canonical CM31 powering for every u64 exponent.
J10623 proves actual tcheb and its finite repetition. J10625 identifies the
complete reversal with reverseBits. J10628 derives the deployed generator
and exponent from owned point execution. J10632 proves one node and J10634
the nine-cell source array. J10636 identifies the point with the stored circle
point. J10640 proves nodeValue u d = doubledFactor (storedFirstLineX18 u) d,
using the cleared-bit identity (J10631) and the existing 2^31 period proof.
No concrete field-power table or large domain is normalized.

J10620 rejects an annotation on an abbreviation; J10621 uses a keyword as a
theorem name. J10624/26/30/33/35 are scalar/cast/parser/transparency drafts.
J10627 is retired by dependency preflight before compiler invocation. J10629
omits zero_mod. J10637 reaches the unchanged 200000 heartbeat limit while
reducing a coordinate projection; J10638 replaces it with a named coordinate
equality. J10638/39 then expose a rewrite syntax issue and a redundant rfl.
No limit is raised and no unchanged failed input is replayed. Every rejected
diagnostic is retained. Accepted axioms are standard only.

Kani reversal-v1 proves the complete owned 18-bit reversal equals native
reverse_bits for every valid index (0.358 s, 130580 KiB). Alignment-v1 proves
native shift alignment and the cleared-bit reversed index formula for every
valid index/depth (0.391 s, 131192 KiB). Both exit 0, zero swap, optimized and
capped. Native power's square/mul binding and complete native node-array
constructor binding remain separate.

Accepted compiles (all exit 0; revision and exact hashes in each receipt):

| Attempt | Exact module | Wall | Peak RSS KiB | Swaps |
|---|---|---|---:|---:|
| J10619 | AspisR1ProducerRelease47.EncoderNodes54 | 0:01.44 | 2641244 | 0 |
| J10622 | R1Z.ProverCommitEncoderPower54 | 0:02.11 | 4114776 | 0 |
| J10623 | R1Z.ProverCommitEncoderDoubling54 | 0:01.90 | 4113212 | 0 |
| J10625 | R1Z.ProverCommitEncoderReverse54 | 0:02.11 | 4117692 | 0 |
| J10628 | R1Z.ProverCommitEncoderPoint54 | 0:02.20 | 4108880 | 0 |
| J10631 | R1Z.ProverCommitEncoderAlignment54 | 0:00.74 | 1647784 | 0 |
| J10632 | R1Z.ProverCommitEncoderNode54 | 0:01.81 | 4114956 | 0 |
| J10634 | R1Z.ProverCommitEncoderNodes54 | 0:02.12 | 4121100 | 0 |
| J10636 | R1Z.ProverCommitEncoderCircle54 | 0:01.90 | 4110296 | 0 |
| J10640 | R1Z.ProverCommitEncoderGeometry54 | 0:01.91 | 4103248 | 0 |

## Stage 4: owned eval_at and encode_at equal both exact encoders

J10641 lifts all derived base-field nodes into WideExact. J10644 checks the
combined owner extraction, whose retained node/collector/phi declarations are
byte-identical. J10645 connects all 256-coefficient evaluations to
exactFinalEncoder. J10646 proves the extracted complete eval_at result.
J10648 proves the complete extracted encode_at result: every one of its four
canonical outputs equals exactInitialEncoder at childIndex u s. The input
point, all nine nodes, channel arrays and phi image are conclusions. No
point/node/channel/model image is supplied. This is the complete owned
WideExact computation; native M31/QM31 instantiation and caller bindings are
still separate.

J10642/43 reject an ambiguous name, numeral/array cast transparency and an
implicit sum rewrite. The replacement uses opaque operations, an explicit
length cast and an explicit symbolic Fin sum bridge. J10647 fixes the
InitialMessage namespace by using its actual function carrier. Limits stay
unchanged. All accepted printed axioms are standard.

| Attempt | Exact module suffix | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| J10641 | R1Z.ProverCommitEncoderLift54 | 0 | 2.02 | 4104960 | 0 |
| J10644 | AspisR1ProducerRelease47.EncoderComplete54 | 0 | 1.10 | 2633060 | 0 |
| J10645 | R1Z.ProverCommitEncoderLine54 | 0 | 2.84 | 4107044 | 0 |
| J10646 | R1Z.ProverCommitEncoderExact54 | 0 | 3.30 | 4102044 | 0 |
| J10648 | R1Z.ProverCommitEncoderInitial54 | 0 | 2.54 | 4110112 | 0 |

Complete-owner Charon/Aeneas exit 0/0, 2.054/0.498 s,
212504/77968 KiB, zero swap, capped and optimized. Full receipts pin source
revision and hashes. No shared object or shipped crate/program is changed.

## Stage 5: native field method specializations

The generic owner uses the byte-identical native scalar.rs CodeField trait.
Extraction succeeds, including M31/QM31 used methods and generic entry points.
J10649 rejects the complete unused inverse records: a native M31 power shift
is emitted with an i32 operand, and two inverse bodies refer to a missing
backend Option-branch constant. Those diagnostics are retained; no external
axiom or template is installed. J10651 selects the exact generic encoder and
used conversion/add/sub/mul bodies. The unused inverse records are explicitly
excluded. This is a used-method projection, not a complete full-record port.

J10654/55/58/57/64 prove the generic collector, evaluator, four channels, phi
and composed leaf. J10661/63 discharge the local arithmetic laws from the
actual extracted M31/QM31 used methods. Every unused trait field is arbitrary,
including try_inv; no inverse correctness premise is added. J10665/66/67
prove the generic model bridge and complete generic entry points. J10668
specializes both encode_at and eval_at to M31/QM31. These conclusions include
canonicality and exact initial/final encoder values, with no point/node/
channel or local arithmetic image hypothesis. They quantify an arbitrary
unused trait record, replacing only the four methods actually read. Binding
the unmodified native full CodeField record and standard iterator state to
this projection remains distinct; no whole native caller claim is inferred.

J10650/53/60 are retired by dependency preflight before compiler invocation.
J10652 uses an applied function rather than its definition name in rewrite;
J10656 leaves a generic type in a decide goal; J10659 omits unfolding field.P;
J10662 retains a WideExact base in the generic statement. Each is replaced
with a changed source. No unchanged input is retried or limit raised. All
accepted printed axioms are standard only; exact revision, hashes, dependency
fingerprints, wall/RSS/swap, outputs and rejected diagnostics are in receipts.

The original iterator nth diagnostic was narrowed to all actual power-of-two
lengths and narrow counters (original-even-v3), then stopped again as RSS grew:
exit 1, 175.427 s, 6474100 KiB, zero swap. This is failed evidence, not a
verified contract. The accepted transition contracts continue to establish
only their stated local source-suffix interfaces. Full native iterator-state
and Vec allocation composition remains open.

Accepted compiles, all exit 0:

| Attempt | Exact module | Wall | Peak RSS KiB | Swaps |
|---|---|---|---:|---:|
| J10651 | AspisR1ProducerRelease47.EncoderGeneric54 | 0:01.43 | 2649660 | 0 |
| J10654 | R1Z.ProverCommitEncoderGenericCollect54 | 0:02.31 | 4119232 | 0 |
| J10655 | R1Z.ProverCommitEncoderGenericEval54 | 0:02.61 | 4132788 | 0 |
| J10657 | R1Z.ProverCommitEncoderGenericPhi54 | 0:01.93 | 4114828 | 0 |
| J10658 | R1Z.ProverCommitEncoderGenericChannels54 | 0:01.85 | 4115956 | 0 |
| J10661 | R1Z.ProverCommitEncoderM31Ops54 | 0:01.62 | 4103764 | 0 |
| J10663 | R1Z.ProverCommitEncoderQOps54 | 0:01.76 | 4104920 | 0 |
| J10664 | R1Z.ProverCommitEncoderGenericLeaf54 | 0:01.95 | 4102292 | 0 |
| J10665 | R1Z.ProverCommitEncoderGenericModel54 | 0:02.16 | 4099364 | 0 |
| J10666 | AspisR1ProducerRelease47.EncoderGenericAt54 | 0:01.38 | 2630052 | 0 |
| J10667 | R1Z.ProverCommitEncoderGenericExact54 | 0:01.86 | 4109336 | 0 |
| J10668 | R1Z.ProverCommitEncoderSpecialized54 | 0:01.86 | 4105916 | 0 |

## Stage 6: retained opened/folded leaf values and bytes

J10670 checks new finite leaf-caller extraction. J10673 proves both exact
encoders commute with field embeddings. J10674 derives all four consecutive
folded values; J10682 derives their complete ordered 128-byte model image.
J10681 proves the source nested-array writes for a full opened column.
J10684 proves all 29 columns and all four slots, including canonicality and
exact initial encoder values. J10685 composes the actual per-column coefficient
Results with the opened matrix; no coefficient-array image is a premise.
J10688 derives both C1/C2 ordered byte images at the shipped slot/lane widths.
J10687 composes the complete retained part-53 opening producer with the folded
leaf owner and identifies its 128 bytes with foldedLeaf (Batched.q1 ...).
The existing challenge-representation identities remain explicit. This does
not assert the complete native semantic/opening caller or allocation layer.

The byte results use the retained canonical source-cell codec and its existing
byte gates; native Vec/chain assembly is separate. The owner and composed
source cuts are named explicitly. No whole simulator equality is inferred.

Rejected drafts J10669/71/72/75/76/77/78/79/80/83/86 are retained. They expose
finite-vector elaboration, a shadowed bound, namespace/Array.set ambiguity,
a tuple projection reduction, codec-list helper naming/composition, a source
zero name and opaque-symbol conversion. Replacements use explicit symbolic
extensionality and tuple equalities. No recursion/heartbeat limit is raised.
The source revision and every exact source/dependency hash are in receipts.
The unused inverse template is retained only as diagnostic .lean.txt and is
not installed or imported by any accepted source.

Accepted compiles, all exit 0 and standard-only printed axioms:

| Attempt | Exact module | Wall | Peak RSS KiB | Swaps |
|---|---|---|---:|---:|
| J10670 | AspisR1ProducerRelease47.EncoderLeaves54 | 0:01.18 | 2639680 | 0 |
| J10673 | R1Z.ProverCommitEncoderHom54 | 0:02.24 | 4110280 | 0 |
| J10674 | R1Z.ProverCommitFoldedValues54 | 0:01.95 | 4118060 | 0 |
| J10681 | R1Z.ProverCommitOpenedColumn54 | 0:02.09 | 4123064 | 0 |
| J10682 | R1Z.ProverCommitFoldedBytes54 | 0:01.84 | 4188536 | 0 |
| J10684 | R1Z.ProverCommitOpenedValues54 | 0:02.35 | 4124896 | 0 |
| J10685 | R1Z.ProverCommitOpenedModel54 | 0:01.75 | 4255808 | 0 |
| J10687 | R1Z.ProverCommitOpeningFolded54 | 0:01.98 | 4280420 | 0 |
| J10688 | R1Z.ProverCommitOpenedBytes54 | 0:01.76 | 4261792 | 0 |

## Stage 7: actual iterator states and query interfaces

The Stage-5 iterator-state limitation is narrowed here. Verification-only,
compiler-specific representation observers check the actual public constructors
and universally quantified next-state transitions of Copied<StepBy<Iter<T>>>
and Copied<StepBy<Skip<Iter<T>>>>. The element types are the byte-identical
shipped M31, QM31 and WideExact definitions, with arbitrary raw words, not just
canonical representatives. Constructor proofs establish pointer/end, stride,
first-item and skip state; transitions preserve the schema and return the exact
indexed value. Separate stub_verified harnesses compare that value and state
with owned_read. Exhaustion checks cover every even length through 256.
All raw proofs are pinned to Kani's rustc 1.93.0-nightly
(53732d5e0 2025-11-20), not a different installed rust-src tree.
The compiler and libcore hashes are in native-toolchain.txt; field/scalar pins
and the selected-limb body comparison are in native-source-pins.json.
These private-layout observers are not shipped or portable library theorems.

The full WideExact odd-value comparison was stopped after memory growth;
e-copied-odd-transition-v6 exits 1, 183.572 s, 6553352 KiB, swaps 0.
Its replacement checks an arbitrary limb in 0..8, with the same function body
and an unused selector parameter. The verified-stub comparison is correspondingly
pointwise. Universality over the selector yields all eight word equalities;
no full-record stub contract is claimed for that replacement. The retained
representation and source-body checks make the boundary reviewable.
No memory cap was raised and no failed input was rerun unchanged.

J10691 establishes the symbolic successful-step, exhaustion and finite sequence
induction. J10692 additionally identifies this finite sequence with the extracted
owned strided collector. This connects the state schema and owned list model;
Vec allocation and specialized native collect/fold assembly still need binding.
It is not a theorem about the entire native simulator.

The new complete-owner query wrappers are structurally extracted in v3.
J10694 checks the exact query declarations. J10698 proves the U32-to-Usize casts,
folded q/4 parent selection, and both opened C1/C2 and folded byte images at
those query indices, from the derived coefficient producer. No leaf-array
image is assumed. The complete opening producer remains composed at J10687,
with its explicit challenge-representation identities.

J10695/96 were stopped at 64.01/35.34 s, 5979700/5342072 KiB, zero swap,
when definal equality began expanding leaf callers. Opaque source/model
interfaces and an explicit cast equality replace that expansion. J10697 then
finishes in 1.67 s with a scalar-literal type mismatch; J10698 explicitly proves
the denominator value is 4 and removes the diagnostic trace tactics.
Failed snapshots contain elaborator placeholders; no accepted source does.

Accepted native scopes below all exit 0, swaps 0; MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Each exact command, wall time,
peak RSS, source revision/hash snapshot, reservations, and cgroup are retained
in receipts/<name>/receipt.json, <name>-inputs.json and input-snapshots/<name>.
RUSTFLAGS is -C opt-level=3 -C link-arg=-Wl,--threads=4; expected time is
optimized verification compilation plus one named transition/contract check.
#print axioms is not applicable to Rust verification.

| Exact native receipt | Wall s | Peak RSS KiB |
|---|---:|---:|
| m-copied-layout-v4 | 1.91 | 301000 |
| m-copied-transition-v4 | 6.979 | 579276 |
| m-copied-owned-v5 | 2.721 | 312112 |
| m-copied-odd-layout-v5 | 1.887 | 300860 |
| m-copied-odd-transition-v5 | 15.411 | 1728756 |
| m-copied-odd-owned-v5 | 2.49 | 314232 |
| m-copied-exhausted-v5 | 2.337 | 313768 |
| q-copied-layout-v6 | 1.964 | 300996 |
| q-copied-transition-v6 | 25.517 | 1785848 |
| q-copied-owned-v6 | 37.873 | 664872 |
| q-copied-odd-layout-v6 | 1.941 | 301520 |
| q-copied-odd-transition-v6 | 36.645 | 2842936 |
| q-copied-odd-owned-v6 | 15.994 | 658416 |
| q-copied-exhausted-v6 | 2.469 | 313372 |
| e-copied-layout-v6 | 1.951 | 301156 |
| e-copied-transition-v6 | 92.873 | 5973564 |
| e-copied-owned-v6 | 68.929 | 2596736 |
| e-copied-odd-layout-v6 | 2.078 | 301176 |
| e-copied-odd-selected-v7 | 60.59 | 4516864 |
| e-copied-odd-selected-owned-v7 | 19.561 | 316992 |
| e-copied-exhausted-v7 | 2.53 | 315384 |

Accepted Lean compiles below all exit 0 and swaps 0. Every theorem prints only
a subset of propext, Classical.choice, Quot.sound. Exact revision, source and
dependency hashes, command, cap, raw output and errors are in lean/J*.json.

| Attempt | Exact module | Wall | Peak RSS KiB |
|---|---|---|---:|
| J10691 | R1Z.ProverCommitEncoderIterator54 | 0:01.92 | 4116012 |
| J10692 | R1Z.ProverCommitEncoderIterator54 | 0:02.12 | 4116224 |
| J10694 | AspisR1ProducerRelease47.EncoderQuery54 | 0:01.26 | 2628928 |
| J10698 | R1Z.ProverCommitLeafQuery54 | 0:01.81 | 4274336 |

## Final coherent audit, integrity and stopping point

J10699 checks R1Z.ProverCommitAudit54 after the new query roots are green.
It imports all 46 new roots and the part-53 retained audit, and prints all
99 new public theorem axioms plus the unchanged deployed headline (100 reports).
Exit 0; wall 1.71 s; peak RSS 4402824 KiB; swaps 0; source revision
`578b7788aa224cdec18581ad42a4d576f9a161fb`; source SHA256
`368a632da087c52c91693e626841679eb8fc4a37af6128b79d251721ba4695af`. Exact dependency hashes, full axioms output,
command and cap are in lean/J10699.json. All reports use only subsets of
[propext, Classical.choice, Quot.sound]; two have no axioms.

The prior J10693 audit covered 44 roots/97 theorems. The new query source is
why J10699 is necessary; no unchanged audit is rerun. This is a coherent
import/axioms audit against the pinned compiled closure, not a full frozen
manifest release replay. No formal release or whole native refinement is
claimed. No unrelated runtime/adversarial suite is repeated.

final-integrity.json and its runnable harness check all 47 live Lean sources
(the 46 roots plus audit) against successful exact-source receipts; every new
theorem is included in the final axioms audit. No live proof hole, new axiom,
native_decide or increased recursion/heartbeat limit is present. The selected
extraction declarations and the old binding manifests are refreshed from v3;
retained complete/leaf declaration bodies remain byte-identical to their
accepted compile snapshots. The one trailing space in an extracted generic
signature is retained to preserve the exact binding. All committed evidence
is text; no binaries, objects, LLBC or archives are included.

The endpoint module and both complete before/after snapshots have SHA256
c263163f19b84438834a6ac25be6164d7e1ad4882fc904813090ca655dfda723.
No file under crates/ or programs/ changed from the actual task base
4af6a0f6bf (LOG D179). The shipped-file ELF rebuilding rule is not triggered.
No wallet or account key is created, destroyed or changed.

**Stop: the assigned J10600–J10699 allocation is exhausted.**
attempt-inventory.json accounts for all 100 numbers. J10627/50/53/60 are
retired by dependency preflight without compiler invocation; J10601 is a
launcher refusal after the missing-cache-artifact failure. No number outside
the allocation is used. No new Lean attempt is launched after J10699.

The complete owned encoder, exact stored-domain nodes, eval_at/encode_at
models, generic M31/QM31 used-method specializations, and owned opened/folded
leaf values/ordered bytes are established. The retained complete opening
producer composes with the folded owner. The native iterator constructor,
next and exhaustion checks cover lengths through 256; the 1024-coefficient
channel check is still a remaining-suffix transition, not the original
Range/Map/array::from_fn iterator-state/collect proof.

The following native bindings remain before asserting native sim_e_ablated
output equals R0Z.RefPayload.simE payload:

- Bind native eval_rec/encode_at guarded recursion and complete Vec allocation,
  optimized collect/fold and four-channel array construction to the extracted
  owner. The state induction and checked local reads do not themselves prove
  native allocation or caller composition.
- Bind the complete native nodes_for constructor and native CM31 power path;
  owned geometry is proved, while native reversal/alignment are checked cuts.
- Bind the native 26 base-column projections and three extension-column c0
  projections, their field embeddings, byte Vec/chain assembly and query maps
  at sim.rs:435–451 to the proved opened/folded leaf interfaces.
- Discharge semantic/opening caller guards, interpolation/original-round and
  challenge provenance, then compose the retained commitment programming and
  serialization results into the complete native caller.

The demonstrated full CodeField extraction obstruction also remains for a
literal full native record: unused inverse methods produce the signed shift
operand and missing Option/residual external template described in Stage 5.
No such template is admitted. The accepted record projection quantifies over
unused methods and proves every method actually used by the encoder; it must
not be described as extraction of that complete native record.

The exact next native consumer is the encode_at calls inside sim_e_ablated's
opened loop and eval_at calls inside its folded entry closure. Their owned
query consumers are ProverCommitLeafQuery54.opened/folded, now green. A new
compile allocation is required for the missing source caller composition.
RustProverRefinement is unchanged; no premise is silently removed, and the
full target is **not established**.

## Verbatim endpoint before

The following definition and deployed theorem signature are copied verbatim
from the full endpoint snapshot; the intervening compatibility lemmas and
proof body remain in endpoint/before.lean.txt.

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))
```

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
```

## Verbatim endpoint after

These excerpts are byte-identical; the full after module is retained separately
as endpoint/after.lean.txt and equals the live deployed module.

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))
```

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
```

## Stage commits through the final proof input

```text
578b7788aa Verify exact iterator state transitions and derive query leaf images
32b230b07f Derive retained opened and folded leaf values with ordered byte images
0823787dde Prove generic encoders and native scalar method specializations
7aa38a6afd Connect complete owned encoders to exact initial and final models
9fdc4c91fa Record exact node geometry evidence and rejected drafts
3c77c18fb2 Prove owned node geometry against the exact stored domain
f7562d6a89 Record encoder stage evidence and native projection boundaries
9219c71bf9 Prove owned encoder values and verify native adapter transitions
718e63dc68 Extract owned encoder and prove finite strided collection
```

The subsequent final commit contains the audit source/receipt, integrity checks
and this completed handoff. Nothing is pushed.
