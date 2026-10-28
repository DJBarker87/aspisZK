# U04 headline slot classification — stage 1

Classification: **(a) for every requested slot; none is class (b)**.
Rows below mean **not a soundness obligation: universally quantified**.
They are submitted for the lead's ruling and are deliberately NOT marked CLOSED.
No dictionary, adapter-law premise, theorem binder or trust item is added.

## Exact headline and definition path

Replayed kernel statement: `evidence/replay-deployed2-20261027/RPx_Deployed.kernel.lean.txt`:

```lean
(missing : AspisR1.IDa_Deployed.Uninstalled CoreError) (indexError : CoreError)
(reservation : AspisR1.NP6_StdModel.Reservation)
...
AspisR1.IDa_Deployed.deployedConfiguration CoreError missing indexError reservation
```

The complete statement quantifies `missing`; it has no separate law restricting
its adapter fields. Its extraction/accepted-run premises still refer to that
SAME selected dictionary and native execution: universality is not removal of
these remaining premises or proof of arbitrary native-to-model correspondence.

Cohort source is `RPv_sources/RPv_IDa_Deployed.lean`, SHA256
`a63aaba9f04bba9b35d5d2429d81ee0774633505619ab3c066d4970b1449a88d`.
Read-only snapshots are retained in `NBU_COHORT_DEFINITIONS.json`.
Exact defining excerpts:

```lean
structure Uninstalled (CoreError : Type) where
  adapter : AdapterRw.Ops
  currentBase : AspisR1CurrentCaller.Ops
  stageBase : VTop_Stages.Ops
  reserved : Bool
  query : Port3_NativeQueryBody.Ops
  geometry : Port3_NativeGeometryBody.Ops CoreError

def seed ... : DrvC_Installation.Configuration FIo_Install.W CoreError where
  adapter := missing.adapter
  ...

def deployedConfiguration ... :=
  FIq_Install.configuration indexError (seed missing reservation) reservation
```

Installed path (all paths are definition names in the replayed cohort):
`IDa_Deployed.seed → FIq_Install.configuration → FIp_Install.configuration
→ Rc5_Install.configuration → Rc3_Install.configuration → DrvC_Installation.sdk
→ SdkD_PairBatches.dictionary`. Selected outer adapter updates install other
fields (e.g. CPP_Install installs op35/op36); the requested fields are retained.
`NBK_DeployedCallbackSelection.registry/policy_accounts` and
`NBN_AccountCallbackObstruction.request_unconstrained` independently establish
SDK field retention for any Configuration. The inherited SDK retention lemmas are kernel-checked; the outer installed
configuration path here is read-only statement/definition inspection. No fresh
whole-headline replay is claimed.

For EVERY following row, exact per-slot excerpt is
`(missing : IDa_Deployed.Uninstalled CoreError)` + `adapter := missing.adapter`
+ `(DrvC_Installation.sdk c).opN = c.adapter.opN` (N as in row), with c the
installed `FIp_Install.configuration indexError (deployedConfiguration missing
indexError reservation) reservation`. Thus it remains `missing.adapter.opN`,
not a fixed installed interpretation. The complete kernel statement is reused,
not freshly replayed at this inspection stage.

| Slot | Native family | Classification | Status |
|---|---|---|---|
| op15 | identity / verifier policy | (a) universally quantified via `missing.adapter.op15` | not a soundness obligation: universally quantified; lead ruling pending |
| op23 | ASQ8 request decoder | (a) universally quantified via `missing.adapter.op23` | not a soundness obligation: universally quantified; lead ruling pending |
| op25 | V1 registry paused | (a) universally quantified via `missing.adapter.op25` | not a soundness obligation: universally quantified; lead ruling pending |
| op26 | V1 registry immutable | (a) universally quantified via `missing.adapter.op26` | not a soundness obligation: universally quantified; lead ruling pending |
| op27 | V2 registry paused | (a) universally quantified via `missing.adapter.op27` | not a soundness obligation: universally quantified; lead ruling pending |
| op28 | V2 registry immutable | (a) universally quantified via `missing.adapter.op28` | not a soundness obligation: universally quantified; lead ruling pending |
| op29 | V2 entry active | (a) universally quantified via `missing.adapter.op29` | not a soundness obligation: universally quantified; lead ruling pending |
| op30 | V1 entry active | (a) universally quantified via `missing.adapter.op30` | not a soundness obligation: universally quantified; lead ruling pending |
| op31 | V1 registry decoder | (a) universally quantified via `missing.adapter.op31` | not a soundness obligation: universally quantified; lead ruling pending |
| op32 | V2 registry decoder | (a) universally quantified via `missing.adapter.op32` | not a soundness obligation: universally quantified; lead ruling pending |
| op33 | V1 entry decoder | (a) universally quantified via `missing.adapter.op33` | not a soundness obligation: universally quantified; lead ruling pending |
| op34 | V2 entry decoder | (a) universally quantified via `missing.adapter.op34` | not a soundness obligation: universally quantified; lead ruling pending |
| op48 | master account decoder | (a) universally quantified via `missing.adapter.op48` | not a soundness obligation: universally quantified; lead ruling pending |
| op49 | checkpoint account decoder | (a) universally quantified via `missing.adapter.op49` | not a soundness obligation: universally quantified; lead ruling pending |

## Consequences and validation

Registry status/retirement/required-binding/reserved scans and master/checkpoint
16-sequence decoding are below class-(a) callback boundaries. They are not
reclassified as CLOSED native bridges. No class-(b) member is identified by the
headline inspection. U04 first-byte/output-lane are independent fixed source
helpers and remain eligible for direct P6 work. U03/U05 ASF8 work continues.

Source/artifact target: frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387,
default f8c0ec72…, devnet 63ad3e9c…, Pool 121f3e29… (inherited, not rebuilt).
Validation: read-only kernel/source/retention inspection; 0 Lean compile
attempts, 0 Kani runs. No new top theorem at this stage; axioms audit N/A.
No source, feature, wire-format, toolchain or release artifact changed.
Headline security target remains not established.

The replay packet intentionally retains the historical FJv descriptive comment: RPx_HANDOFF.md and RPx_statement-comparison.json certify the complete RPx kernel type is byte-identical. The quantified payload, not that comment, is the authority.
