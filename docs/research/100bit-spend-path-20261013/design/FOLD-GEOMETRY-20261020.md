# R17 fold and stored-domain commutation — 2026-10-20

Status: symbolic commutation proved; complete deployed R17 remains OPEN.
Base revision: f2c084bc8f51c02f4c58b6d0a4e3dd450867e1f5.
Branch: codex/cx-geometry-20261020. No Rust or existing Lean module changed.

The format is the adopted compact binary multiproof format
(`LEAD-REVIEW-FORMAT-ADOPT-20261020.md`). These facts change neither root
bytes nor transcript rows: roots remain absorbed as 32-byte digests at the
same rows. This packet supplies algebra and geometry for R17, not R13/R14,
acceptance, transcript composition, or a security theorem.

## Checked definition map

| Runtime definition | Actual model definition | New theorem |
|---|---|---|
| `crates/aspis-core/src/r0/domain.rs:48–58`, children/parent/slot | `lean/NaturalProjection.lean:30–61`; AspisFormal `V5ComponentCConcreteFoldLinearity.lean:207` | `FoldStoredGeometry.child_eq_model`, `query_parent_slot` |
| core `domain.rs:68–75`, exponent `1024+4096 rev18(u)` | `AspisFormal/AspisFormal/V7ExactOneFoldDomains.lean:138–145` | `fibre_eq_stored` |
| core `domain.rs:97–99`, `2*x²-1` | `V7ExactOneFoldDomains.lean:348–373`, `storedFirstLineX18` | `x18_eq_stored` |
| `fast_domain.rs:282–299`, two table lookups and line node | same stored fibre / log-18 node | `FoldFactoredDomain.factored_fibre`, `tables_to_stored` (explicit table premises) |
| `verifier.rs:114–126`, line fold | `V5ComponentCConcreteFoldLinearity.lean:117–137`, nested `lineFoldValue` | `FoldRuntimeAlgebra.line_eq_model`, `FoldGeometryBridge.line_at_stored` |
| `verifier.rs:105–112`, circle fold | same nested fold at `(y,-y,x)` | `FoldRuntimeAlgebra.circle_eq_model` |
| `verifier.rs:141–145`, x/y/z denominators | `lean/Line18Geometry.lean:57–167`, `V5FriReleasedLineGeometry.lean:33–64` | `runtime_y`, `z_eq_model`, `x16_eq_stored`, `quartet_t4` |
| `transport.rs:4,14–18`, τ and bitwise loop | `lean/D18Transport.lean:13–16,143–171`, `rowNat`/`rowEquiv` | `FoldD18Commutation.sourceRow_eq_rowNat`, `sourceRow_inverse`, `coefficients_rows` |

All AspisFormal paths above are relative to `AspisFormal/AspisFormal/` unless
fully spelled out. Runtime paths without a crate prefix are relative to
`crates/aspis-r1-cost-probe/src/`. New Lean modules are in this design tree's
sibling `lean/` directory. The local cache names `R1Line18Geometry`,
`R1NaturalProjection`, and `R1D18Transport` are the established names of
`Line18Geometry.lean`, `NaturalProjection.lean`, and `D18Transport.lean`.

## Signs, index maps, and tables

For arbitrary parent v and slot s, child reversal is
`rev18(4v+s) = rev16(v) + 65536*rev2(s)`. The reversed low digits are
`[0,2,1,3]`; the line points rotate by `g^(2^29*rev2(s))`.
The model's stored quartet is `[x0,-x0,x1,-x1]`. Runtime `y` is slot 3,
so `y=-x1`, and `(d-c)/(2y)=(c-d)/(2x1)`. There is no sign discrepancy.
The line fold is the nested model fold with inverse tuple
`((2x0)^-1,(2x1)^-1,(2z)^-1)`. The circle fold uses
`((2y)^-1,(-2y)^-1,(2x)^-1)`. Nonzero hypotheses are explicit, as required
by recovery; the successful source zero guard is at `verifier.rs:145`.

`sourceX18` interprets the core line-node expression. `sourceX16` is two
more doublings at child zero, exactly the two-fold branch of
`verifier.rs:217–218`. Both are proved equal to the stored model tables;
`quartet_t4` proves independence of the child slot. `z_eq_model` identifies
the intermediate denominator with the stored log-17 coordinate.
These are pointwise function equalities, never an enumeration of 2^18.

The fast-domain split is also symbolic:
`rev18(u)=512*rev9(u%512)+rev9(u/512)`. Thus table A's exponent is
`1024+2097152*rev9(lo)` and B's is `4096*rev9(hi)`. Their product has the
source fibre exponent. `tables_to_stored` makes the two table-content
hypotheses explicit. `evidence/fold-geometry-20261020/table-validation.json`
independently checks all 512 entries of each actual Rust table by modular
complex repeated squaring. This is arithmetic validation, not a new kernel
certificate or a claim that the conditional table theorem has no premises.

For τ=[3,4,2,0,1], `sourceRow` spells the five runtime shifts, masks and ORs
literally over Nat. `pack_digits` proves the ORs are additions without
carries. The resulting function is exactly the existing `rowNat`, so the
existing involution and coefficient/row round trip apply. This is a theorem
about the bitwise expression, not an Aeneas loop execution theorem. Variant D
uses a different retained D13 lookup (`transport.rs:15`); no D18 statement is
asserted for that arm. `weights.rs:124–126` builds factors in the same TAU
order; `weights.rs:148` reads low digits least-significant first. Its
WideExact/QM31 arithmetic and mutable tensor loop need the S3/S6 re-pins;
those execution refinements are not consequences of a digit-permutation
identity.

## Existing pinned source results and remaining re-pins

The gap map's historical “no Lean mentions” description predates these
packets at the present base:

* `evidence/session-b-fibre-point-stored-domain-20261020/sources/` contains
  `R17FibrePointStoredDomain.successful_fibre_point_eq_stored`. It connects
  actual extracted fast-domain arrays and all-index power certificates to
  `storedInitialFibrePoint20`, with explicit CM31 operation laws, checked
  lookup results, and mask/shift index facts. This is stronger than the new
  independent constant validation; it is not silently replaced by it.
* `evidence/session-b-query-denominator-slots-stored-20261020/sources/`
  contains `R17QueryValuesSlotsStored.emitted_success_slot_values`: the exact
  emitted helper's successful five returned slots equal stored circle x/y,
  log-18 child-zero/child-three x, and `2*lineX²-1`. The helper may take an
  `anyCheck` callback; its semantics are not automatically supplied.
* `lean-candidates/geometry-zero-test-instance-20261020/README.md` identifies
  the actual-input owner `R17QueryValuesEntryActualDefsV1` (source SHA
  `14893288a301656546585eb2bf7a39997c9009caf0a51ba385c53487ef3a3de3`).
  Its composition obtains nonzero decoded slots from successful execution,
  with a source-shaped std `SliceIter`/`any` specialization.
* `lean-candidates/geometry-stored-inverse-20261020/sources/GeometryStoredInverse.lean:47`
  (`grouping_success_stored_inverse`) connects the checked candidate
  composition and grouping callback to the matching stored denominator's
  inverse; `grouping_success_canonical` additionally gives canonical words.

These are pinned extraction/component results and candidate compositions,
not a theorem about the entire frozen production body. S7 remains the
required dependency for `QueryGeometry::for_range` (`verifier.rs:133–163`):
original input/prefix iterator equivalence or adoption, Rust std `any`
semantics, whole map/from_fn/collect construction and ordered grouping,
`for_query` bounds, and frozen caller integration. The new scalar
`batch_inverse_entry` and `batch_inverse_step` justify the algebraic invariant;
they do not prove that every Vec iteration executes it. The new
`line_with_inverses_eq`/`circle_with_inverses_eq` prove the optimized fold
expressions agree once the supplied tuple is the matching inverse tuple.

The field interpretations are explicitly marked as specifications in the new
modules. They are not renamed “source execution” theorems. The R14/S7
extraction must connect the real WideExact/M31 operations, constant quarter
and half embeddings (`weights.rs:6`, `verifier.rs:118`), success and
canonicality to these expressions. No additional source extraction was run
or fabricated in this packet.

`CertRelData.rel_data` in
`docs/research/v8-r0-zk-20261009/lean/R1Z/CertRelData.lean:54–62` takes
`hL0,hL1,hL2,hX` as explicit premises. In particular the extracted `x16`
argument is an input slice (`CertRelExtracted.lean:421,495`), not a table
constructed by that function. Identifying an arbitrary such input with
storedLine16X is false: the table `storedLine16X + 1` differs at index zero.
`FoldGeometryBridge.unconstrained_table_counterexample` checks that
obstruction over any field. The construction/decoding premise must remain;
only the actual domain computation is covered by `x16_eq_stored`.

## Verification and scope of receipts

`FoldRuntimeAlgebra.line_recovers_channels` directly consumes
`lean/LineFold.lean:86` (`AspisR1.recovered_horner`); it is not merely a
similar-looking recovery statement. `FoldChildPowers.line18Point_child_pow_four`
is the group-valued L1.3 statement from `L1-L2-REPEATED-LIFT.md:86–87` for
arbitrary v and s. `FoldGeometryBridge.natural_poly_child` connects the
actual `naturalLinePoly` (`CircleNaturalBasisEval.lean:38`) via
`naturalLineValue_eq_eval` (:46) and `naturalLineValue_four_mul`
(`V5FriNaturalBasisRadix4.lean:75`) to the source child and stored log-16
point. No concrete coefficient/domain table is expanded.

Every local attempt has a command, source SHA, raw output, `/usr/bin/time -l`
log and receipt under `evidence/fold-geometry-20261020/`; `manifest.json`
includes failed attempts as well as successful ones. New sources were
compiled against the recorded base revision plus their exact working-tree
source SHA; the containing commit records those sources. Each compile uses
an exclusive mkdir lock, `-j1 -M4400 -DElab.async=false`, the pinned Lean
4.32 binary and a private `/tmp/cx-geometry-20261020-objects` output directory.
The unchanged `LineFold.lean` dependency is compiled once to that private
directory because no matching cached module was available. Existing modules
and shared object directories are not edited or overwritten.

Dependency fingerprints identify resolved direct imported objects. Early
fingerprints were reconstructed before extending the algebra module's
imports, as marked explicitly in the receipts; later fingerprints are
captured before execution. These focused cache-based checks are not a claim
of a fresh, coherent full release rebuild (D63 remains applicable).
`FoldGeometryAudit` is the single final focused root, not a full frozen
release-manifest replay. No unchanged full regression, Rust gate, SBF build,
or generated certificate aggregation was run: production sources did not
change. A release replay must include these new modules after the S7/R14
source refinement and the ordinary manifest preflight.

Final result: **31 new theorem reports**, all standard axioms, from the
exit-zero `FoldGeometryAudit` root (5.580 s, 2,300,821,504-byte peak RSS,
0 swaps). Eight final module/dependency targets pass. The largest accepted
focused target is `FoldStoredGeometry` (26.623 s, 4,037,033,984 bytes,
0 swaps); none raises the 4400 MiB Lean cap. `accepted-summary.json` gives
the exact final source hashes, receipt paths and results. Earlier failed
attempts are retained and excluded, including timeouts from elaboration;
the replacements use explicit child-index and recurrence lemmas rather than
raising limits. Complete deployed R17 remains open on the named source
execution/refinement boundaries above.
