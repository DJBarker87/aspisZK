# D545 EVH8 handoff — full native task remains unfinished

Continue ONLY in /Users/dominic/ZK/.worktrees/pv-evh, branch
codex/pv-evh-20261029. Baseline 0da088f6f87a20db01518eb53c95e2343f7b47bf.
Same prompt chain/rules; no delegation, push, crates/programs/soundness edits,
extracted-source edits, other worktree writes, native or Kani runs. New modules
PV_EVH_. Receipts evidence/pv-evh8-20261101/. **Rows removed NONE.**

## IDs / budget / host

Charged 23 attempts: 14 accepted,
9 failed; 57 of 80 remain.
Focused 79300–79396; audits 79397–79399 UNUSED. The 736xx block is retired.
Next fresh ID 79323; its admission has been refused, so it remains UNCHARGED.
Retry SAME ID only after FULL 180-second cooldown from latest refusal epoch;
up to ten retries. Read refusal-history files to count. Never bypass admission.
Same-shell exit zero AND allowed:true, one scope, 6G/8G/swap0/tasks64, -M7000.

Reuse /home/dombarker/project-offloads/codex-pv-evh-20261029 and all caches.
Own stage/compile/audit tools under tools/pv-evh8-20261101/. No host infrastructure
changed. Current stage snapshots can be reused on admission-only retries when
source/dependencies have not changed. A new accepted dependency needs staging
for its consumer, not rebuilding predecessors. All imports remain in the
inherited coherent project/external cohort; no library extension.

The historical restoration gate is ALREADY CLEARED, despite the removed temp
flag. Committed pv-evhd/rules.json records reading the flag and its hash/size;
pv-evh5/resume-D540.json already recorded its later absence with explicit resume
authorization. restoration-resolution.json records this evidence. Do not create
another bootstrap hold or treat a missing asynchronous owner answer as approval.

## Accepted work and its exact scope

OpeningInstall.install_fixed and OpeningProver.entry_fixed install the source
PrepareOpening / FinishOpening / PublishCompact spines into the actual extracted
RealR1_client.prove_for_proof_accounts entry. PublishCompact exposes the source
Vec.with_capacity let as an effect-capable native leaf; ValueBind's generic
law is axiom-free. Allocation failure is not erased or assumed source-success.
All sixteen prepare / thirteen finish / fourteen publish leaves remain native
obligations, including the capacity leaf. This is Result transport, not native
trace adequacy.

NonzeroStep / NonzeroFlow interpret the actual entropy_nonzero32 source loop,
without a whole-helper answer. NonzeroInstall / NonzeroProver install this same
interpreter at the outer nonce guard and the inner entropy-block checks. The
remaining entropy structure has six native leaves. NonzeroSafety (79319)
proves the active array read is bounded, increment cannot wrap, source step is
total, and step interpretation equals the source-primitive lift. Generic scalar
proofs; no concrete 32-byte normalization. Full loop completion is next.

PrivateSaltStep (79314) and PrivateSaltsStep (79317) are accepted source spines.
PrivateSaltsStep required distributing a match continuation and then normalizing
ONLY the source Result bind association. The generator permanently emits that
proof. PrivateSaltsFlow / SaltsProver are committed but UNCOMPILED.

All accepted axioms are standard or empty; per-ID receipts record revision,
blob/SHA, dependency fingerprint, target, exit/wall/RSS/swap and printed axioms.
All jobs stayed below cap, swap zero, no memory kill or limit increase. Refusals
were uncharged. Source failures and changed replacements are retained.

## Important native gap found (do not lose this)

In the actual loaded extraction, core.result.Result.map aliases ExternalFuns.op11
and map_err aliases op12. The old generator's language-level lift whitelist
therefore hides native operator/callback/drop obligations. This does NOT refute
accepted Result transport, but prevents promoting entry_fixed's Compatible
hypotheses to full native coverage even if those hypotheses are discharged.

native_preflight.py (--check) permanently inventories SEVEN such lifted sites
in the selected source spines and says native coverage OPEN. --require-native-closure
fails while any remain. Native callback purity alone does NOT bind the external
operator! entry-open-native-leaves.json gives 109 explicit fields PLUS these
aliases and runtime/boundary obligations; it is a TEXTUAL census, not coverage.

PrivateSaltWrap (UNCOMPILED) defines an independently interpreted pure newtype
constructor/map. Its map_fixed/map_agrees require an EXPLICIT sourceMap op11
installation; actual opsNative association remains OPEN. Its Rust constructor
body is byte-identical across extraction/current source and is just Self(values),
with no allocation in that body. Later vector drop stays OPEN.

ResultOps (UNCOMPILED) gives source op11/op12 models and native event operators
with explicit eventful callbacks and unused-closure drops. Callback semantics
owns consumed capture/argument drops and unwinding. It proves Result transport
only under its explicit dictionary selection, callback FinishedView and silent
successful-drop view. It does NOT prove actual dictionary/native adequacy.

VariantGuard (UNCOMPILED) gives the three-constructor comparison and event-free
retry guard at an explicit op233 dictionary. Actual opsNative installation is
OPEN. Existing source value definitions are ProverRwCallerBinding.variantEq,
ProverRwSuccessOptions.resultMap, and PDict_RejectionStdSource.core.result.Result.map
(read through git show only; not imported, no cohort substitution). Reuse their
actual source bindings when available; do not credit a fresh model dictionary.

## Exact next proof actions

1. Retry 79323 PV_EVH_NonzeroTotal after cooldown, reusing its current prepare.
   Last charged Total failures 79320–79322 were proof elaboration, never memory.
   Current committed replacement unfolds NonzeroFlow.loop, rewrites the explicit
   PrefixLoop.loop equation, reduces tuple projections, then rewrites stopStep.
   This replaces a failed definitional change at the zero/terminal branch.
   The successor invariant and final concrete bind already elaborated in 79321.
   The intended result is: fuel >= remaining+1 and i.val+remaining=32 gives
   finished .ok with unchanged world/events []; run 33 and source totality follow.
2. Compile PrivateSaltsFlow, then SaltsProver. Their inputs use explicit tuple
   state lambdas and dsimp before source loop case splits, avoiding prior errors.
   PrivateSaltsFlow/PrivateSaltWrap/VariantGuard are already staged against known
   dependencies; ResultOps staging may have completed (check prepare record).
3. Compile ResultOps, PrivateSaltWrap and VariantGuard; fix source/elaboration
   errors only with changed bytes. These are LOCAL operator laws, not (v') links.
4. Bind actual remaining native effects: allocation/heap/address/errno channels,
   zeroize/drop, paths/digests/options, hash/oracle bytes, checked failure/panic/
   abort and EVERY reached formatting path under fmt-1. Current World only has
   file/oracle/counter state; it does not itself provide heap/handle fidelity.
   Preserve every mutable-borrow restoration. No whole-helper OS answers.
5. Only after full native coverage: unchanged oraclePrefix, countTrace and
   nonce-store fileTrace projections. Never infer empty native projections from
   FinishedView. D520/U/D524 client/account inputs remain explicitly named.
6. Only after actual-family/provenance-fixed links: (v') reduce to successful
   actual worldRun at runjoin opsNative AND its allocator world. NativeObstruction62
   and op132 still prevent inferring uniform success. No unrelated MODEL witness
   earns credit, and advancing reject-then-success entropy need not have a uniform
   dictionary view. No new T field or hidden source/native trust is authorized.

Run audit.py read-only reconciliation before final handoff. Audit IDs and one
full closure/manifest replay remain reserved until actual acceptance is ready.
No native/Kani, wallet/key/funds operation, push or release claim occurred.
