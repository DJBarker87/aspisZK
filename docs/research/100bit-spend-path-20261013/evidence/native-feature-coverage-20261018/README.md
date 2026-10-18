# Accepted6dd native feature audit

Read/hash-only audit of `6dd9028e9`: no Cargo, compiler, Lean or native job.
`feature-audit.json` pins both accepted archives, all six receipts/runner/input
manifest/log hashes, source manifests and actual verbose rustc invocations.
The reader distinguishes active `--cfg feature=...` from permitted `--check-cfg`
values. Dependency `--extern` edges confirm the resolved build, beyond CLI flags.

| Gate | Explicit Cargo features | Effective cost-probe features | Prover |
|---|---|---|---|
| codec1233-final | r0,pool-v1-kernel | cost-probe not compiled for gate | N/A |
| saved-proof-counter-final | none | default,private-leaf-salts,prover | enabled by counter dependency |
| checkpoint23-final | pool-adapter,private-leaf-salts | default,optimized-terminal,private-leaf-salts | **absent** |
| verify-real-s2-default | prover,private-leaf-salts,optimized-terminal | default,optimized-terminal,private-leaf-salts,prover | **enabled** |
| verify-real-s2-detail | preceding +detail-phases | default,detail-phases,optimized-terminal,private-leaf-salts,prover | **enabled** |
| query-migration-102 | prover,private-leaf-salts,optimized-terminal | default,optimized-terminal,private-leaf-salts,prover | **enabled** |

Cost-probe defaults are empty. The checkpoint program defaults to custom-heap;
its actual test cfg is custom-heap,default,pool-adapter,private-leaf-salts. Its
cost-probe dependency enables optimized-terminal and forwards private-leaf-salts;
the archived dependency rustc line has no prover cfg or aspis_prover extern. This
establishes checkpoint23's no-prover build without another run.

Both accepted verify test modes explicitly enable prover. Their module guards
also require prover, so removing the CLI flag alone would run zero injections.
The report lists the necessary test-only adaptations for deployed-shape coverage.
The accepted runs remain valid for their recorded feature configuration. No
without-prover verify injection result is claimed here. Query102 likewise retains
its actual prover-enabled status. Counter's manifest explicitly enables prover
even though the counter CLI has no feature flag. Codec is a statement/codec gate
and does not establish verifier configuration coverage.

Reproduce with `python3 tools/r1-native-feature-audit/audit.py --check`.
