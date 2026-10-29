# D519 resume of the pre-registered measure strengthening

The target, observer, simulator, original bad event, numerical envelope and
three-field T remain those fixed in ../pv-meas-20261029/DESIGN.md. This document
records the authorized implementation route, not a claim of checked results.
Branch codex/pv-meas-20261029; resume source 304384c21ee320de826bfb04ec4399872ec5bbcd.

## Authority and cohort, before proof attempts

D519/h4' authorizes the pinned Mathlib 81a5d257c8e410db227a6665ed08f64fea08e997
extension under (a)-(c). cohort-check.json checks all 203 source blobs against
that revision and all 206 frontier object hashes against the unchanged original
manifest d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e.
Every frontier candidate package object also byte-equals its authority object.

Candidate .trace files contain aggregate depHash and output hashes, without
per-import input hashes or an equivalent recorded generation fingerprint.
Those records alone do not discharge (b). The conservative reconciliation is a
fresh rebuild of every one of the 203 modules, in dependency order, against the
authority and the earlier rebuilt extension modules. No candidate object is
accepted because its timestamp or frontier matches. Each rebuild has its own
74000-74999 ID, admission and capped scope (6G/8G/swap=0, Lean -M7000), and is
uncharged. The overlay contains hash-checked plain copies and companions of the
authoritative Mathlib namespace; effective-authority.json implements first-root
namespace resolution. No shared object or original manifest is edited.

The addendum is written incrementally, with its own SHA. It is NOT a usable
203-module extension until all 203 modules succeed. Preparation refuses a
partial addendum. Per-module receipts record the direct dependency fingerprint;
transitive fingerprints follow by the frozen topological chain.

## Proof route and before/after

1. Average and transport: arbitrary ProbabilityMeasure, Bochner integrals,
   bounded measurable decisions and measurable conditional probabilities.
2. Uniform: symbolic finite sums of Dirac measures, cardinality normalization,
   exact integral/rational-mean bridge and finite pushforward law identification.
3. Coupling/Fuel: native R and common S arbitrary measured spaces. Both D163
   marginals are exact maps. The old fuel/seed/query event on the finite MODEL
   coordinate and its existing finite mass theorem are unchanged.
4. Core: reuses the cryptographic finite-model proof and bounds; native/model
   agreement uses the unchanged context/timing/signal links.
5. Deployed: arbitrary environment/native/acquisition/common laws. Exact joint
   acquisition is identified by a pushforward equality. ConditionalLaw specifies
   its environment-indexed native law on bounded measurable tests; no native
   independence, truncation, conditioning or public clock is assumed. Nine
   source links, V400, causality, adaptive observer and selected callback remain.
6. Satisfiability: an explicit synthetic model must satisfy the WHOLE measured
   conjunction, including all measure laws. It is not a native execution.
7. Legacy: every old finite link conjunction maps to the measured conjunction.
   The old rational event inequality must follow from the measured headline and
   exact integral/cast transport, without invoking the old headline theorem.

Before: Fintype Env/R/N/S with uniform rational means. After (TARGET): arbitrary
measurable Env/R/N/S and probability laws; only cryptographic model coins retain
their required finite uniform law. A measurable decision is used on the SAME
full Signal x Observation carrier. No side channel or failure prefix is removed.
Rows removed: NONE. This is a representability strengthening. All native source
association, joint acquisition, D163/D166 and original T obligations remain.
Measurability and conditional-law identification are explicit measure versions
of the former finite law interfaces; they do not assert privacy as a hypothesis.

## Budget and audit order

100 charged Lean attempts, IDs 73100-73199; 73197-73199 reserved for statement,
axioms, and final frozen import-manifest replay. Zero Kani/native runs.
First proof compile: PV_MEAS_Average, then Uniform/Finite, Coupling/Fuel, Core,
Deployed, simultaneous witness, Legacy corollary. No project draft earns credit
until elaborated. Failed proof sources are changed before any resubmission.
