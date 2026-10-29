# Single authorised aggregation

Worktree `/Users/dominic/ZK/.worktrees/pv-evhc`, branch `codex/pv-evhc-20261029`, input HEAD `5e9df8eb46b7ba32cde9b0eb430d93f5fc41fffd`. User authorization cites Stream A LOG D526. The user supersedes the historical NOT AUTHORIZED fields in AGG16-REQUEST and READY only for this one compile; READY remains authoritative for the environment. Receipts belong here. No source changes, Stream A rebuilds, pushes, or dependency compiles were performed.

## Preparation

The unchanged consumer hash is `2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4`. The reconciled cohort hash is `f8ff7cfcc649f1b99a01b0703353d4856a472ac198884cb80b706863b9d07d65`; NDR authority is `cbd00ba461b8b8e683d15eaf460e1d317ddedf55b2b5e2309e4fcf2b6d035dd8`; first-root preflight is `31e9cb1ed3ac4c9b2c5a89e1f5bda7dbd8d8a2092eea6a5d69a5e5bb13dbab4a`. `verify.py` checks all effective objects and companions read-only. `preflight-parser-correction.json` records an own-script ID-parser correction before any admission; this was no hash discrepancy or compiler attempt.

## Statement and nonvacuity audit

The exact three final statements are in STATEMENTS.md, extracted from the frozen source with every binder retained. The source snapshots used for the audit are adjacent `.audit-source.txt` files. NDR and FixturePdaRuntime are taken from revision `06f74c902f`; NDR source hash is `fdfd7c55f0b99a38a588bd0730878534f697d7f0e872e1529a4c89b560aeb794`, blob `b527950aa5e0f45c7e6921fd38d883a4eafc53ed`.

`public_fibre` has an unconditional model witness for every byte handle. CallerLive derives its public equality from the pinned request, lane index and frontier bytes and consumes the existing V047 fibre. It does not associate arbitrary native handles, traces or live requests with that fixture.

`two_transaction_nonvacuity` uses `AspisR1.NDR_CombinedAudit.sourceOnHeadline` directly. For each `base`, `stage`, `slot` **and explicit `runtime : AspisR1.JHu_FixturePdaRuntime.FixturePdaRuntime base`**, it supplies one saved vector shared by both TX1 worlds, its exact checkpoint bytes and length 1768, and successful TX2 on the same installed headline SDK. No equality of the two TX1 heaps is asserted. The tree and byte SHA realizations were discharged in the inherited NDR theorem; the runtime premise remains.

`instance_nonvacuity` is the same conditional joint witness projected through the exact wrapper-call triple `deployedInstance`. It neither removes the runtime premise nor establishes arbitrary live reachability. `FixturePdaRuntime base` is the seven-enumerated-call equality `∀ seeds program, Call seeds program → base.op38 seeds program = JHs_PDA.derive seeds program`. It remains an unproved native runtime/ABI/model association, with the valid-memory and compute conditions described in its source. No runtime law is promoted into trust.

**The fixture witness does not prove the event acquisition or joint simulation links.** There is no simultaneous satisfiability proof here for the conjunction of the event skeleton's acquisition and simulation hypotheses; that skeleton remains UNVERIFIED under D485. The conditional fixture execution witness is narrower. No privacy endpoint premise is removed, added or changed. Native trace/template/handle/source-provider associations, allocator/abort conditions and the compiler boundary remain. The privacy target is not yet established.

## Execution

Final preflight passed; execution stopped after the one failed compile. The launch guard permits one marker and no resubmission. Admission must return `allowed:true` and exit 0 in the launch process; exit 78 or allowed:false waits 180 seconds and retries at most twenty times. The only large scope is 14G high / 16G max / swap 0 / TasksMax 64 with Lean `-M15000`, ID 70700. Timeout 600 seconds enforces the ten-minute review point.

## Final result and exact receipt

**FAILED; attempt 70700 consumed; no retry.** Final hash preflight passed for 16,583 modules and 33,182 object/companion files in 59.406266 seconds. No required hash differed. Zero small dependency compiles ran. IDs 70701–70799 were not submitted. Runner copies were byte-identical to the lead-owned originals; `verified.json` records their full hashes. `launch.py` guard SHA-256 is `2be10cabcadc0d7585eb8e404603e876abaed21cf65d3e417f7836bd2d84d015`.

Admission `host-resume4/admission-70700-0.json` returned `allowed:true`, and `admission-exit-70700-0.json` records exit 0. Existing bounded reservation was 8 GiB; requested reservation was 16 GiB, within the 55 GiB limit. No reservation refusal or cooldown retry occurred. Admission and scope launch were performed by the same invocation of `launch.py`. The exclusive `LARGE-ATTEMPT-STARTED.json` marker prevents another submission.

Exact target: `PV_EVH_FixtureConsumer`, `sources/PV_EVH_FixtureConsumer.lean`. Command (cwd `/home/dombarker/project-offloads/codex-pv-evhc-20261029`):

```text
systemd-run --user --scope --quiet --unit=pv-evhc4-70700 -p MemoryHigh=14G -p MemoryMax=16G -p MemorySwapMax=0 -p TasksMax=64 python3 /home/dombarker/project-offloads/codex-pv-evhc-20261029/S2W_lean_host_agg16.py resume4/attempt-70700.json
```

The runner executed:

```text
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake env lean -j1 -M15000 -DElab.async=false -o objects/PV_EVH_FixtureConsumer.olean sources/PV_EVH_FixtureConsumer.lean
```

LEAN_PATH, verbatim:

```text
/home/dombarker/project-offloads/codex-pv-evhc2-20261029/objects:/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean
```

Compiler and launcher exit: **1**. Wall: **5.664144367910922 seconds**. Peak RSS from `/usr/bin/time`: **4,521,784 KiB**. Swaps: **0**; cgroup swap maximum **0**. Raw cgroup memory peak: **1,072,943,104 bytes**, retained separately from the time RSS metric. All asserted cgroup caps matched. Source revision: **5e9df8eb46b7ba32cde9b0eb430d93f5fc41fffd**. Full receipt, time and output: `lean-70700/{receipt.json,time.log,stdout.log}`. No timeout, memory exception, or OOM occurred.

Exact error:

```text
sources/PV_EVH_FixtureConsumer.lean:1:0: error: import AspisR1WithdrawalValidation.Types failed, environment already contains 'instDiscriminantPoolV1PaymentStatementFormatErrorIsize' from R1Z.BuilderAdmissionExtracted
```

`isolation.json` pins both loaded objects; `collision-source-excerpt.txt` identifies the existing provider's generated discriminant declaration. This is a declaration-name collision when the two otherwise hash-verified import cones are combined, before consumer elaboration. Hash and first-root coherence alone did not detect declaration disjointness. There was no recurrence reduction to isolate and no memory cap increase. No source or environment repair was attempted after the single large attempt.

**Full consumer #print axioms result: unavailable.** Output contains zero axiom lines because import merging failed before any consumer declaration or query. This is not an axiom-free result. `AXIOMS-AUDIT.json` records all four requested queries as not reached. The statement/nonvacuity audit above is a frozen-source audit only; this failed attempt does not certify those consumer declarations. No successful consumer object, proof, nonvacuity validation, or privacy premise removal is claimed.

The next concrete deliverable is a lead-approved resolution of the generated declaration collision between the EJR-selected builder extraction and the pinned withdrawal extraction, preserving their source/provenance and statements, followed by separately authorized validation. This job's compile budget is exhausted. The fixture witness does not prove the event acquisition or joint simulation links; FixturePdaRuntime base remains explicit. Target not yet established.
