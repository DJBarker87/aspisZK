# Two-transaction privacy non-vacuity audit

Status: **STOP at the explicitly permitted missing-bridge condition.** No privacy
premise was removed. No AGG16 request is ready. The deployed privacy target is
not yet established.

Branch: `codex/pv-2tnv-20261028`.
Base: `96f705ea1a630300a7b9dbcd79161bf7adc074c9` (inherited prover candidate).
All inspected source revisions, git blobs and SHA256 hashes are in
`SOURCE-AUDIT.json`. Read-only Stream A sources were inspected with `git show`;
no Stream A compiled objects were loaded. Both JHx and JHw handoffs were read.
The shared rules, all LEAD RULING updates and host-restored flag were read first.

## Exact joint statement and retained hypothesis

`JHx_Joint.source.lean.txt` preserves the complete inspected theorem source.
`JOINT-CONCLUSION.lean.txt` is the byte-for-byte conclusion extracted from that
source, excluding the `:= by` delimiter. Write `J base stage slot` for precisely
that Prop, with the source's opens/namespaces. This is notation in this report,
not a new Lean declaration or a claim of successful elaboration.

The existing result is exactly:

```lean
AspisR1.JHx_Joint.source
  (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : Aeneas.Std.U64)
  (runtime : AspisR1.JHu_FixturePdaRuntime.FixturePdaRuntime base) :
  J base stage slot
```

Its conclusion supplies one saved vector, original-world TX1 acceptance,
corrected-world TX1 acceptance, equality to the checkpoint bytes, length 1768,
and actual TX2 wrapper acceptance. Both TX1 expressions and TX2 use the same
installed SDK selection. Original and corrected heaps remain distinct.

`FixturePdaRuntime base` is **NOT discharged**, **NOT adopted for privacy**, and
**NOT added to T**. Its exact value law is:

```lean
∀ seeds program,
  AspisR1.JHu_FixturePdaRuntime.Call seeds program →
  base.op38 seeds program = AspisR1.JHs_PDA.derive seeds program
```

It covers the seven enumerated calls, with the ABI/memory/compute/runtime SHA
and decompressor qualifications in its source. It supplies no privacy carrier,
public-record association or experiment refinement.

## Carrier audit and exact missing bridge

Fix the SAME `CommitHandle`, `Aux`, `template`, `outputs`, `x`, `rust`,
`observer_program`, `Fintype rust.RealRand` and `Nonempty rust.RealRand` as the
existing headline. Define the following notation by literal endpoint expressions:

```lean
K := R1Z.PrivacyR1AcctBasis.K
H := R1Z.PhaseWireLog2Bin.honest R1Z.PrivacyR1HeadlineDeployedReal.input
Ref := R1Z.PrivacyR1HeadlineDeployedReal.RustRealRefinement
  template outputs x rust observer_program
```

The first missing carrier bridge, expressed exactly without weakening any
quantifier of the headline, is:

```lean
(base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : Aeneas.Std.U64)
(runtime : AspisR1.JHu_FixturePdaRuntime.FixturePdaRuntime base)
(p : J base stage slot) :
  ∃ (adv : rust.Adversary) (w : H.Instance), H.public w = x.1
```

For the stronger request that the headline's *premises* are jointly satisfied,
the missing statement additionally needs the unchanged `Ref`:

```lean
(base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : Aeneas.Std.U64)
(runtime : AspisR1.JHu_FixturePdaRuntime.FixturePdaRuntime base)
(p : J base stage slot) :
  (∃ (adv : rust.Adversary) (w : H.Instance), H.public w = x.1) ∧ Ref
```

These are obligation signatures, NOT checked or asserted theorems. They cannot
hold for every free `rust`: `FSExperiments.Adversary` has no inhabitance field.
Keeping the other carriers fixed, setting Adversary to Empty and defining its
functions by empty elimination is permitted by that interface. J mentions no
rust and is unchanged. Thus the joint theorem cannot imply the first signature
for arbitrary headline parameters. This is a definitional interface argument,
not a Lean-checked counterexample or a runtime counterexample.

A useful existential specialization instead needs a *specified deployed*
`rust`, a concrete member of its Adversary carrier, a native fixture statement
`x`, and a canonical `w` with `H.public w = x.1`. It must prove that this x/w
encodes the very native input/proof whose returned bytes occur in J, and that
`rust.real` executes that input with the installed SDK of J. No such association
map/law is present in J. Choosing x from an unrelated mathematical fixture and
conjoining its fibre theorem with J would not establish this same-execution
association.

For full premise satisfiability, the specialization must also supply `Ref`
above. Its exact definition quantifies over EVERY matching w and EVERY adv,
and requires Nonempty of `ProverCommitFuelJoin22.RunJoin` between the paired
runtime view/observer result and source view/observer result with the exact
old-bad and seed-query functions. RunJoin includes a coupling with exact
marginals and agreement outside the existing bad event. One deterministic
accepted wrapper execution supplies neither that distribution nor that
agreement. The observer and simulator must remain those of the endpoint.

Existing `PV_RunJoin_CanonicalFixtures.Association transferX withdrawalX`
leaves precisely these native public associations as explicit fields:

```lean
transferX.1 = R1J.SpendWitnessMap.mapPub
  (R1Z.PV_RunJoin_FixtureRecords.fixturePublic false)
withdrawalX.1 = R1J.SpendWitnessMap.mapPub
  (R1Z.PV_RunJoin_FixtureRecords.fixturePublic true)
```

Neither equation is a conjunct of J. Those lemmas prove mathematical fibres;
their comments explicitly retain native public/byte association. No proof of
the missing same-execution bridge was found in the inspected interfaces.

## Ledger disposition: before and after

| Row | Before | Result of this audit |
| --- | --- | --- |
| V045 | Free rust; deployed source instance/refinement absent | Retained. J establishes conditional fixture wrapper acceptance, not an FSExperiments implementation or its RustRealRefinement. |
| V046 | Arbitrary rust.Adversary may be empty; chosen R1Adv already evidenced | Retained for arbitrary rust. Existing `PV_RunJoin_Source.observer_nonempty` inhabits R1Adv independently of J. Identifying that carrier with the deployed rust remains necessary. |
| V047 | Mathematical fixture fibres already evidenced; arbitrary-x/native association retained | Retained. J contains no canonical RspendPlus witness and no equation between native fixture public bytes and H.public w. It cannot supply a matching fibre for arbitrary x. |

Thus the new joint result supports the **execution-acceptance component** of a
future same-fixture non-vacuity theorem, conditional on its named runtime law.
It does not itself close any of these three privacy ledger rows. No assumption
was discharged, added, moved, or changed in the privacy endpoint. T remains
exactly entropy_law, entropy_kernel, observation. No simulator, observer,
headline quantifier or implementation was edited.

## Validation and AGENTS.md formal-release fields

This handoff is a source/statement audit, not a formal release result. There
are no new Lean declarations. Exact imported statements were read rather than
elaborated; proposed bridge signatures above are explicitly unverified.

| Field | This job |
| --- | --- |
| Exact compile target | None: stopped at user-mandated missing-bridge condition |
| Exit status | N/A; no compiler launched |
| Wall time | N/A; no compiler launched |
| Peak RSS | N/A; no compiler launched |
| Swap | N/A; no compiler launched |
| Source revision | `96f705ea1a630300a7b9dbcd79161bf7adc074c9`; other inspected inputs individually pinned in SOURCE-AUDIT.json |
| #print axioms | Not run here; existing JHx handoff reports standard axioms only, reused as reported evidence, not a fresh audit |

Budget used: **0/60 normal Lean, 0 Kani, 0/1 coordinated AGG16**.
No env-J IDs consumed (60900–60999 remain unused by this job, including audit
IDs 60997–60999). No admission request or capped scope launched. No full replay,
local Lean compile, library build, extraction, runtime test or ELF rebuild ran.

Created the requested host directory by SSH, exit 0:
`/home/dombarker/project-offloads/codex-pv-2tnv-20261028/`.
No sources or compiled caches were uploaded. No transport retry was required.
The sparse checkout was extended only with `git sparse-checkout add
evidence/pv-2tnv-20261028`; there was no full checkout. No crates/programs,
existing proof sources, shared host sources, wallet keys or artifacts changed.

The source/conclusion snapshot was mechanically compared with the pinned git
blob, and evidence file sizes were checked below 20 MB before commit.

## Stop and next deliverable

The explicit instruction "If the witness does not connect to the privacy
headline's carriers without a further unproved bridge, state that bridge
exactly and stop" governs this outcome. Therefore no theorem asserting the
missing association, no final consumer, and no AGG16-REQUEST.json were created.
Spending compile budget on independent carrier inhabitants or a conjunction
with unrelated fixtures would not resolve the missing bridge.

Next deliverable: a source-grounded fixture input/public/witness encoding and
deployed FSExperiments identification, proving the same-execution association
above. If full headline premise satisfiability is intended, also prove its
unchanged RustRealRefinement for that instance. Only after those are proved is
the normal-cap implication followed by a lead-run AGG16 consumer warranted.
