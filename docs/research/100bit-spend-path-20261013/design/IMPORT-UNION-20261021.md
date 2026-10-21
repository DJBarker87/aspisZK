# Combined cone imports — 21 October 2026

Branch `codex/cx-import-coll-20261021`, base `f01405274`. Existing modules,
Session A candidate directories, other workers' files and shipped sources are
read-only. All experimental sources and receipts are under
`evidence/import-coll-20261021/`. This is an import integration experiment;
no soundness premise is removed.

## Inventory

The environment inventory enumerates kernel constants in each of the three
retained R22 audit groups, including implicit declarations, readers,
constructor/projection/recursor declarations and wrappers. A second raw-object
scan follows the original three import DAGs and reads each project module's
`ModuleData.constNames` separately. This also retains duplicate equation
lemmas hidden by the environment's accepted-theorem deduplication.
`raw-duplicate-declarations.json` is the complete differing-module inventory;
`duplicate-declarations.json` records the four cross-group environment
overlaps found first. Shared library owners are excluded, and common imports
of the same module are not collisions. The scope is the reported three-group
obstruction, not every archived extraction elsewhere in the repository.

| Name(s) | Defining modules / extraction |
|---|---|
| `instDiscriminantErrorIsize` | `AspisR1PublicPreparation.Types` (public preparation); `AspisR1S3InactiveSource.Types` (`s3_inactive_source_cut`); `Stage2ContinuationTypes` (`aspis_r1_cost_probe` stage2 continuation) |
| `instDiscriminantVariantIsize` | public preparation Types and stage2 continuation Types |
| `instDiscriminantPhaseIsize` | public preparation Types and stage2 continuation Types |
| `Aeneas.Std.Array.make.eq_1` | `AspisR1EbyKPushWideToQ`, `AspisR1WideToBytesIndexedCandidate.ToBytesGeneratedOutputV11`, `AspisV8R19.SqueezeSourceExecution`, `S3InactiveModelBridge`, `S3VariantRowBodyProbe` |
| `Aeneas.Std.Array.make.congr_simp` | `AspisR1EbyKPushWideToQ`, `ExtractedQM31SamplerBytes` |
| `AspisR1CandidateParser.optionDiscriminant.eq_1` | `ActualDecodeKFieldParserTransport`, `R1CandidateParserSupport` |
| `AspisR1CandidateParser.optionTag.eq_1`, `AspisR1CandidateParser.optionTag.eq_2` | same parser wrappers |
| `Aeneas.Std.Isize.ofInt.congr_simp` | same parser wrappers |
| `AspisR1CandidateParser.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual.eq_1` | same parser wrappers |

There are **10 duplicated names: 3 incompatible instance definitions and 7
compatible generated theorems**. `raw-module-graph.json` records every
inspected project's module path, hash and direct imports.

The first three names denote definitions (typeclass instances), not identical
shared types. Their enum types and `read_discriminant` functions already have
different fully qualified names. The common `M31`, `CM31`, `QM31` and layout
spellings are beneath distinct extraction namespaces; there is no additional
shared Types definition name in the enumerated union.

The seven generated-theorem overlaps are allowed: Lean 4.32's `Lean/Environment.lean` explicitly
permits different modules to prove the same theorem with the same type, to
support on-demand equation lemmas. Proof bodies may differ by proof
irrelevance. It must be distinguished from duplicate instance definitions.
The combined prototype checks this distinction in the actual union.

The untouched baseline fails with:

```
import AspisR1S3InactiveSource.Types failed, environment already contains 'instDiscriminantErrorIsize' from AspisR1PublicPreparation.Types
```

## Proposed fix and prototype

The evidence-only `ImportUnionNamedDiscriminant` adapter calls the pinned
`Aeneas.Discriminant.generateReadDiscriminantCmds` and elaborates its reader
command unchanged. It replaces the anonymous instance command with
`<fully-qualified-enum-name>.instDiscriminant`. On copies only, the S3 and
stage2 Types modules import the adapter and replace `@[discriminant isize]`
with `@[import_union_discriminant]`. All five affected enum readers retain
the original generator logic (S3 Error; stage2 Error, Variant, Arity, Phase).
Public-preparation Types/Funs and the entire main group are reused unchanged.

Thirteen copied modules are rebuilt, bottom-up, into
`/tmp/codex-cx-import-coll-20261021-objects`; this directory alone overrides
the old S3/stage2 objects. No shared cache is written. Wrapper changes are
only additional axiom-print commands; statements and proofs are unchanged.
`copy-provenance.json` pins every original and copied source.

| Focused check | Exit | Wall (s) | Peak RSS (bytes) | Swaps |
|---|---:|---:|---:|---:|
| Untouched union baseline | 1 | 5.567 | 2,317,189,120 | 0 |
| `ImportUnionAllConesCx20261021` | 0 | 6.606 | 3,234,267,136 | 0 |
| `ImportUnionHeadlineCx20261021` (R19 + all cones) | 0 | 7.200 | 3,558,064,128 | 0 |

The raw scan covers 157 project modules and 5,473 declaration entries; the
13-module rebuilt closure exactly equals the transitive dependents of the
two changed Types roots. `dependent-closure-check.json` records this equality.

The all-cone module imports **all three** retained R22 audit groups in one
Lean environment and prints 60 standard-axiom audits. The headline aggregator
additionally imports the unchanged `R1FinalSoundnessBinPerQueryR19` and audits
its `final_soundness` theorem to `[propext, Classical.choice, Quot.sound]`.
The equation theorem overlap coexists, as Lean's import implementation allows.
These are focused integration checks, not a replay of the full frozen manifest.

Every attempt uses the requested local toolchain, `-j1 -M4400
-DElab.async=false`, the global mkdir lock, and `/usr/bin/time -l`.
Receipts include source revision/hash, immediate-object dependency
fingerprint, exact command/path, exit, wall, peak RSS, swaps, complete axiom
output and errors. Three initial adapter elaboration errors are retained;
the fourth adapter version passes. The raw inventory extension also retains
one failed IO-monad elaboration before its corrected version passes. There was no memory failure or cap raise.

## Source files, extraction provenance and ownership

Paths below are relative to `docs/research/100bit-spend-path-20261013/`,
except the upstream Aeneas library. The full declaration census is in
`inventory-{main,row,constant}.json` and `raw-inventory.json`; the raw scan
also includes compatible duplicate lemmas inside each group.

| File | Extraction / role | Owner and required action |
|---|---|---|
| `lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean` | Public-preparation c16 extension: `transport.Variant` line 302, `verifier.Error` line 336, `verifier.Phase` line 392. Corresponding Funs is in the same directory. | Public preparation / **Session A S1 and S10**. No source change needed for the tested fix; reused cached objects. |
| `lean-candidates/s3-s9-current-repin-20261020/AspisR1S3InactiveSource/Types.lean` | `s3_inactive_source_cut`, `r0.Error` line 15. Funs imports this Types. | **Session A S3 and S10**. Do not apply the experimental attribute substitution to their live candidate. Recompile with the adopted naming fix. |
| `lean/Stage2ContinuationTypes.lean` | `aspis_r1_cost_probe` continuation: `verifier.Error` line 81, `transport.Variant` line 95, `multiproof.Arity` line 135, `verifier.Phase` line 170. | Stage2 / S5/S8 source owners and R22 integration; **Session A S10** owns final import coverage. Recompile with the adopted naming fix. |
| `S3InactiveExecutionBridge`, `S3InactiveModelBridge`, `S3VariantInactiveComposition`, `R22TotalRowCones`, `R22TotalRowPacketAudit` | Transitive S3 wrappers | Session A S3/S10 and R22 packet owner. Rebuild objects only; no theorem edits required. |
| `R22Stage2LocalBodies`, `R22Stage2ControlBounds`, `R22Stage2LeafTotal`, `R22TotalStage2Constants`, `R22TotalConstantPacketAudit` | Transitive stage2 constant wrappers | Stage2/R22 owners; S10 imports. Rebuild objects only. |
| `../v8-full-view-zk-20260912/lean/AspisV8R19/SqueezeSourceExecution.lean` and `lean-candidates/s3-s9-current-repin-20261020/row-output-equation-v7-v1/sources/S3VariantRowBodyProbe.lean` | Squeeze and row wrappers trigger `Array.make.eq_1` generation | Squeeze owner and **Session A S3/S10**. No change required; duplicate theorem types are compatible. |
| Upstream `Aeneas/Data/Discriminant.lean` | Generates the anonymous instance syntax | Toolchain/extraction lead. Proposed central fix below; no upstream file edited here. |

The public Types object selected by the retained cache is pinned to
`e1d3e2db77e3e3730db804bb1a32d75546a18b4929a4e38a3017afd489450922`.
Existing `evidence/finish-point-and-terminal-call-20261018/prefix-extension-provenance.json`
ties the c16 canonical Types hash `34d88375…` to the tx1 extended source hash
`a2b07cd9…`, which matches the source path above. Other copies of
`AspisR1PublicPreparation/Types.lean` are listed with hashes in
`public-types-source-variants.json`. They provide alternative sources for one
Lean module; the search path chooses one provider, not all versions at once.
They must not be confused with distinct-module declaration collisions.

The other compatible generated-theorem owners are the parser wrappers
`lean/ActualDecodeKFieldParserTransport.lean` and
`evidence/lean-candidate-field-parsers-20261014/sources/R1CandidateParserSupport.lean`
(S5 parser extraction/support),
`lean/ExtractedQM31SamplerBytes.lean` (sampler wrapper),
`evidence/s5-to-bytes-indexed-proof-v1/lean/ToBytesGeneratedOutputV11.lean`
(indexed-byte serializer wrapper), and
`lean-candidates/eby-k-constructor-and-source-push-20261020/sources/AspisR1EbyKPushWideToQ.lean`
(S4/S5 EbyK bridge). These files need no naming edits; Session A S4/S5/S10
must retain their pins. Generated `.eq_*` and `.congr_simp` declarations are
created on demand by tactics, explaining why a plain declaration-text search
would miss them.

## Adoption recommendation

The least invasive permanent change is **type-qualified instance emission in
the Aeneas discriminant attribute library**. `proposed-aeneas-naming.patch`
shows the two-line naming change against a retained source snapshot. The
reader, scalar type, explicit discriminant values and generic binders remain
unchanged. This central change leaves the generated Types/Funs source bytes
as generated; rebuild their objects and the dependent wrappers with a newly
pinned library. The generalized library patch is a proposal, not an installed
or independently compiled toolchain patch. The closed-isize adapter implements
the same naming mechanism and is the implementation actually checked here.

The exact **tested** alternative is the evidence prelude plus the two copied
Types edits in `copy-provenance.json`; all other copied sources differ only
by audit commands. It avoids touching the public-preparation extraction and
changes five instance names, four of which actually collide in this union.
This alternative requires owning sessions to adopt a naming adapter or
emission change; the worker has not edited their modules.

No Charon or Aeneas extraction command was run. There are **no extraction CLI
flags used or claimed** for this fix: the collision is introduced while Lean
elaborates the discriminant attribute, after extraction. The tested commands
are recorded verbatim in each `command.json`, with this shape:

```
LEAN_PATH=<recorded ordered paths, private objects first> \
  /Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -j1 -M4400 -DElab.async=false -R <evidence>/prototype \
  -o /tmp/codex-cx-import-coll-20261021-objects/<module>.olean \
  <evidence>/prototype/<module>.lean
```

A shared Rust-type prelude is unnecessary and would require additional
cross-extraction type-identification work: these Error types are genuinely
distinct (the S3 enum has seventeen constructors; the verifier enum has
eight). Re-extracting entire cones under new namespaces would also rename
all downstream theorem types while failing to fix the anonymous root name
at this attribute layer. A root import aggregator alone cannot repair an
import error before its own commands run. The successful aggregator uses
newly rebuilt, explicitly named instance definitions; it is not a namespace
wrapper around incompatible existing objects.

## Release boundary and reproducibility

No theorem, hypothesis or conclusion was weakened or removed. The headline
and `R1FinalSoundness` source files are byte-identical to base `f01405274`;
`endpoint-signature.diff` is empty. No new soundness endpoint is claimed.
The R19 boundary `h_R22 : s.R22` and all other residuals remain explicit.

`tools/import-union/validate.py` checks every attempt's source snapshot,
receipt, resource fields, final-source hash, public-theorem axiom audit and
the exact permitted copy transformation. It checks that the endpoint sources
are unchanged and that every repository change is a new file in this task's
three allowed locations. Failed baseline/adapter attempts are retained and
excluded from accepted axiom evidence. The all-cone and headline checks are
the one final combined import audit; no unchanged full regression was rerun.

What remains is adoption by the named owners, re-pinning the chosen Aeneas
library/naming adapter, rebuilding all affected dependents in the canonical
manifest workspace, and one frozen manifest replay. The copied-world result
establishes that this collision is resolvable without changing enum semantics
or any proof statement; it does not itself update Session A's S10 manifest.
No shipped crate/program file, frozen ELF, wallet key or other worker's file
was changed. No Rust/Kani gate or ELF rebuild was required or run.
