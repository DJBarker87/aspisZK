# Rebuild-authoritative private source cohort

No shared source or object is overwritten. `shared-source-differences.json` records exact research and observed shared hashes for three module names. This replay selects the existing rebuild-record source paths at pinned research HEAD, even where the shared loader currently holds a different variant.

| Module | Declarations required by this closure |
|---|---|
| AspisR72Sampler.Types | `AspisR72Sampler.transcript.Transcript` (including `hash`) and `AspisR72Sampler.field.QM31`, consumed by the sampler extraction and exact-field sampler bridge |
| AspisR1ProverCommit.Types | `AspisR1ProverCommit.aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets`, `host_commitment.PrivateSalts`, and the retained verifier/error carriers consumed by `AspisR1ProverCommit.prover.derive_private_salts` and its proof chain |
| R1Z.BuilderAdmissionExtracted | `AspisBuilderAdmissionSource.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate` and `AspisBuilderAdmissionSource.pool_v1.pair_trace.validate_common`, consumed by the builder-admission refinement chain |

These are existing declarations, not new alternate names or weakened interfaces. Research hashes come from the EJR selected/resolved path association, as corrected by ruling (h'). Shared hash differences are reported, not repaired. Final private object receipts determine whether this source cohort composes successfully.
