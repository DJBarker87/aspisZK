# Universal source-identification contract

Entry HEAD 16de37214533ff7736f744b013c5bb05c9b63f33, exact worktree /Users/dominic/ZK/.worktrees/pv-runjoin, branch codex/pv-runjoin-20261026.

BuilderSource.SourceIdentification is parameterized by a field K, the instances [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647], an honest prover source : HonestProver K and toInstance : source.Instance → BuilderCanonical.Instance (K := K). Its exact fields are:

- V152: `public_eq : ∀ w, source.public w = BuilderSource.prover.public (toInstance w)`.
- V153: `build_eq : ∀ w, source.build w = BuilderSource.prover.build (toInstance w)`.
- V154: `transport_eq : source.transport = BuilderSource.π`.

The first two quantify over **every source.Instance**, with no statement-equality guard, fixture restriction, or selector. The third equates equivalences Fin 1024 ≃ Fin 1024, hence every coefficient index. BuilderCanonical.Instance is the subtype of Public M31 × Wspend satisfying RspendPlus after embedding into K. NativeInput.Input itself is raw data, not an admitted carrier: in particular compiled is caller-supplied. NativeIdentification.prover accepts an arbitrary inputs : I → Input; its existing toInstance uses PV_Src_Premises.admission and records extracted from successful compilation. These domain distinctions must be preserved.

The lead correction supersedes runjoin21 REPORT/STAGE1 language about requiring an actual deployment-selected i to prove these universal rows. No further selector search is undertaken. Fixtures are non-vacuity instances only; V038 remains universal over common samples.

Recount 5: 407 rows, 400 P, 3 T, 4 C; OPEN 93. It says “Deployed P remains OPEN, record counts 2/8/6 unchanged” and “Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.” Current row removals 0; endpoint premises removed/added/weakened 0/0/0.
