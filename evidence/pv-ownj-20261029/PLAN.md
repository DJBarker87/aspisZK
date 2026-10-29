# D449 V239 consuming join

Worktree /Users/dominic/ZK/.worktrees/pv-own, branch codex/pv-ownj-20261029,
base 66672e84fb. V239 only. Budget 100 Lean attempts, 30 native scopes, 0 Kani.
IDs 64700–64796 development, 64797–64799 audits. No implementation changes.

Execution/proof order:
1. RawConsumer.value at Scanner.width/trailing/suffix: transport the ordered
   weight fold and row enumeration through the concrete QM31 decoder to dense
   multilinear evaluation (constraints_v4.rs:601–632,782–794).
2. point_claims (:749–760): statement_points outer loop, 29 column inner loop,
   first shape-error return before allocation. At the builder all 29 lengths
   are 1024 (:792–808,826–831).
3. prove_sumcheck (:1587–1627 in state_only_hiding.rs): each callback point
   consists of previous transcript challenges, fixed sample, fixed Boolean
   assignment; final alpha consists of challenges for published rows15–24.
   Bind transcript seed to public.public_bytes and published C1 root, and every
   challenge to published framed bytes, using existing transcript laws where
   available. Initial claim/oracle values may enter published polynomials, but
   must not enter the query point through an unpublished influence channel.
4. Compose owned source execution and PublicPlan.same_public at that instance.

Inherited owni evidence is supporting work, not completed native/dense/public
refinement. Stop/report a checked unpublished point influence or witness-dependent
allocation finding. Otherwise restore only on complete consumed law; preserve
any exact remaining blocker. New proofs compile smallest-first with -M7000,
one admitted scope (6G/8G/swap0/Tasks64) at a time. Reuse caches only after h6
source/object/import checks. Keep V370/D381/D386 and rdea-1 named; T unchanged.
Existing Aeneas/Rust semantic agreement is reclassification within existing tool
trust. Own-2''' applies only to constant subcalls, not these input-taking roots.
