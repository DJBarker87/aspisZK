# NPO_ scoping note: a computable host instance for the row-5 executable check

Stream A, 2026-11-10. This is a scoping note with no proofs. It is based on one read-only scan,
NPO_L035, whose output is NPO_L035/NPO_NONCOMPUTABLE.json (summarised by root in
NPO_NONCOMPUTABLE_BY_ROOT.json). Target not yet established.

## 1. What was measured

NPO_Noncomp2 loads NNH8_Exec and NNH_Run6Installed from the L187 objects, with environment extensions
loaded (`loadExts := true`, `enableInitializersExecution`). From each root it follows definition
values through the constants that Lean has tagged noncomputable. For every tagged constant it records
the cause visible in its own value:

- **classical:** the value mentions `Classical.propDecidable`, `Classical.choose`/`choice`/
  `indefiniteDescription` or `Classical.decEq`;
- **fixpoint:** the value mentions `Lean.Order.fix`, i.e. a `partial_fixpoint`;
- **opaque_ext:** the value mentions an opaque or axiom constant of non-Prop type;
- **inherited:** none of these, but a dependency is noncomputable;
- **no_ir_other:** none of these, and no noncomputable dependency.

The controls behave as expected. `List.map` is computable. `Classical.choose` is noncomputable.
`List.flatten` is tagged noncomputable in Init/Prelude.lean:3127 and runs through its
`@[csimp] flatten_eq_flattenTR` replacement, so its tag is harmless. This also corrects the remark in
the first handoff that NPO_L024's list was "unreliable": the tag was read correctly.

The scan reached 363 noncomputable constants:

| Cause | Count |
|---|---|
| inherited | 294 |
| classical | 63 (57 project definitions plus the Init/Mathlib `Classical.*` and `Exists.choose` themselves) |
| no_ir_other | 6 (5 project definitions plus `List.flatten`) |
| fixpoint | 0 |
| opaque_ext | 0 |

The extracted Aeneas code is computable as it stands. `partial_fixpoint` loops compile through
their implementation, and NPO_L022 compiled `stage1_owned`. Nothing on the path relies on an opaque
external. The noncomputability is entirely in the hand-written model and library layers (LIB_, LIBB_,
LIBC_, NJ*_, NG*_, NMX_, NN*_, Port*_).

## 2. Leaves by root

These counts are the project leaves, excluding the core `Classical.*` constants.

| Root | Noncomputable reached | Leaves | propDecidable | choose | decEq | no_ir_other |
|---|---:|---:|---:|---:|---:|---:|
| `NOC_Run5bCtx.sdk` (host dictionary) | 59 | 12 | 12 | 0 | 0 | 0 |
| `NNH_ReturnsBundle.tx1Value` | 104 | 14 | 2 | 9 | 2 | 1 |
| `NNH_ReturnsBundle.tx2Value` | 85 | 20 | 13 | 6 | 0 | 1 |
| `NNG_TotalProducer345.producer` | 117 | 16 | 5 | 8 | 2 | 1 |
| `NNH_Run6Installed.implementation` (I) | 274 | 57 | 34 | 16 | 2 | 5 |
| all roots together | 363 | 63 distinct | | | | |

The sdk's 12 leaves are all decidability choices:

- `NGL_CheckpointModel.install` and `NGL_ReadonlyModel.install` (`classical; decide (a = b)` on keys);
- `Hist_Authority.keyEq`, `Port3_BatchStd.sameLeaf`, `Port3_FinishStage.ne`, `Port4B_CountInstall.nodeCount`;
- `NHY_PolicyModel.policy`;
- `NJI_MasterModel.model`, `NJI_MasterModel.terminal`, `NJI_V1Models.Z`;
- `NJQ_Checkpoint.model`, `NJQ_Master.model`;
- `NNH_MRegistryOps.install`.

## 3. Refinements, by class

**(a) `Classical.propDecidable` (about 34 sites).** These are `if`/`decide` on a Prop whose instance
was supplied classically: key equality, byte-array equality, and policy and terminal guards. The
computable refinement uses the structural `DecidableEq` (Array/List/UInt8) or a hand-written
`Decidable` instance. Equality with the original is uniform, because `Decidable p` is a subsingleton,
so `decide`/`ite` agree under any two instances: `Subsingleton.elim`, then `congr`. One generic lemma
plus a generated equation per site should do. These are easy.

**(b) `Classical.decEq` (2 sites: `LIB_VCarriers.pDec`, `LIB_VScalarCarriers.qDec`).** These are the
same as (a). Easy.

**(c) `Classical.choose` (about 16 sites).** There are two shapes.

- **Total-Result choice.** Examples are `LIBB_ResultTotal.value r h := Classical.choose (h : ∃ a, r = ok a)`
  and `LIB_VArithmetic.qadd`/`qmul` (`choose (add_total x y)` with `add_total : ∃ v, native = ok v ∧ …`);
  `LIB_VRecords.payload`/`validatedRecord` and `LIB_VMask.maskValue` appear to be the same. The
  refinement is `match r with | ok a => a | _ => default`. It equals the choice because `ok` is
  injective, and the spec gives `r = ok (choose h)`. One generic lemma. Easy.
- **Existential selection with no uniqueness.** These are `NMX_R9_Live241.observation` and
  `NMX_R6_NativeLive242.observation` ("a source selection" from `live …`), `NJQ_ChildTotal.master`,
  `.policy` and `.identity`, `NJM_CircleJoin.point`, `LIBC_ExpandSemanticModel.Row`, `LIB_VClaims.parent`,
  `LIBB_AuthCarrier.raw`, `LIBB_NullifierBytes.digest` and `LIB_VDecode.decodeK29`. Here a computable
  witness can only be proved equal to the choice if the chosen property has a unique solution. Each
  needs inspection: either a uniqueness lemma, or a restatement in which downstream consumers use only
  the spec. The second option is a model change and needs its own review. This is the hard class and
  the main source of variance.

**(d) no_ir_other (5 sites).** `LIBC_Bytes.raw` is declared `noncomputable` explicitly although its
body is decidable (`if h : b.length ≤ Usize.max`), so removing the keyword in a copy suffices.
`NLP_C04Chronology.atEvent`, `NMX_R4_CallRun.observe`, `NNH_064SourceDetails.trace` and
`NNH_MerkleBatchExecute.run` show no cause in their value constants. They need a per-definition
compile probe, probably through a definition compiled without code earlier in the chain.

**(e) Binders that must be instantiated by tables.** These are H (`Bytes → State`, the run's
SHA-256 query table), pda and clock (`Fixed.pda`, `Fixed.clock`), the reservation bit, and the
allocation streams (all-success). All of these are data and computable once given.

## 4. Threading the refinements

The leaves are not definitionally equal to their refinements, so the 294 inherited definitions must
be copied with the leaves substituted. This uses the NPO_Clone mechanism on definitions only, since
the copies are typed by the originals' types. Each copy needs an equation `copy = original`. The
copy's value is the original's value with leaf constants replaced, so the equation follows mechanically
from the leaf equations by `congrArg` over the abstracted value, and a generator can emit and
kernel-check it per definition.

The copies then need compiled code. A native tool can call `compileDecls` on them after import, because
the computable dependencies carry IR in the oleans. The evaluation then runs in the IR interpreter
inside the 8G cgroup. The import alone is 6.8 GB (NPO_L022, NPO_L035).

Run time is the open risk. `Slice` is List-backed, and the verifier indexes the 57,607-byte proof
thousands of times (NPN F2). Interpreted, that may be 10^8 to 10^9 list steps: minutes to hours, not
seconds. A 1-scope timing probe on one library call, for example `LIBC_ParseShape.value`, should come
before any full run. Linking a native executable instead would mean compiling every cone module to C,
which is a far larger build.

## 5. Estimate, in capped scopes

| Step | Scopes |
|---|---:|
| Refinements (a)+(b): generator, about 36 equations, 3 to 5 modules | 5–8 |
| Refinements (c), total-Result shape: one generic lemma plus sites | 3–5 |
| Refinements (c), existential selections (about 10 sites): inspection plus uniqueness lemmas or a reviewed restatement | 10–30 |
| Refinements (d): compile probes and fixes | 2–4 |
| Threading: copy the 294 inherited definitions plus their equations (NPO_Clone variant) | 4–8 |
| compileDecls plus a timing probe of one library call | 2–3 |
| Recorded-pair data modules: images, metas, instruction data, slot, H table, pda table (NPN step 3) | 3–6 |
| The executable run of `I.entry`, tx1Value and tx2Value at the 10 November host on the recorded pair | 2–4 |

The total is roughly **30 to 70 scopes**, dominated by the existential selections. The result would be
executable evidence that the model accepts the recorded pair. It would not prove `Runs`; the R2
per-call proofs remain as in the NPN plan. The refinement equations are reusable there, because a
per-call proof at a computable copy can be transported to the original by the same equations.

## 6. Recommendation

1. Start with the sdk alone: 12 propDecidable leaves, about 6 to 10 scopes including threading. Pair
   it with the 1-scope interpreter timing probe on `stage1_owned` at that sdk. If the timing probe is
   hopeless (hours per call), the executable route for row 5 should be dropped in favour of R2
   symbolic evaluation, and the remaining refinements are not worth building.
2. Separately, have a reviewer decide whether the existential selections in class (c) admit
   uniqueness lemmas. That decides the upper end of the estimate.

Target not yet established.
