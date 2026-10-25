# SbfResolve criteria and execution plan

Entry 65c4082110f0c6f088f85f8d1cf432db0fb1ab89; assigned branch only.
Only tools/sbf-resolve-20261025 and evidence/sbf-resolve-20261025 may change.
No merge/push, builds, scope creation, privilege, namespace, keys, RPC or theorem
execution. Both security targets remain not established; axioms N/A.

Coordination: initial local ps found PID29365 absent (exit1); only then the exact
released output tail was read and its terminal codex-exit=0 observed. No host
access yet. This is coordination release, not resource admission.

1. Read immutable merged SbfClosure/SbfInputs/SbfCachePrep and official tool/source
packets via Git blobs; retain hash/size references and limitations. Research the
primary Cargo ca74c32f0ac6d99000858dcae9b0931ef76a8f43 metadata call path,
config discovery and exact rustc introspection before any Cargo call.
2. Implement and test a small fail-closed Python compiler-query wrapper and
bounded metadata collector. No real compiler calls in synthetic tests. Wrapper
permits only source-justified exact queries, never compilation. Cargo source,
not the wrapper, must exclude build-script/proc-macro execution.
3. After local preparation, inspect released public host inputs and fresh bounded
prep reservation (<55GiB populated finite reservations; >=7GiB control available).
Do not create a systemd scope: this job's scope budget is zero. Use sampled
resident RSS <512MiB and deadlines/output bounds for metadata, no RLIMIT_AS/DATA.
Verify own parent uid/mode/OWNER and known frozen lock/manifest/wrapper pins.
Exclusively create own0700 SbfResolve-20261025-v1; independent HOME/CARGO_HOME/
settings/cwd; no unreviewed ancestor config or credentials. Private copies only.
4. Reuse existing 7978-file frozen source and exact official tools, pin before/
after selected binaries/runtime/helpers and controls. Do not rematerialize source
or replay archive. Copy reviewed123 registry view and118 indices into new private
cache with source association. If source review proves wider resolver discovery,
prepare at most the exact428 locked public registry universe, checksumming data
and safely extracting archive members. New downloads <=32MiB each/256MiB total,
exact static.crates.io URLs only, no same-URL retry. Preserve failed attempts.
5. Charge at most TWO Cargo CLI calls before launch; no version/help calls.
First: metadata --offline --locked --format-version 1 --no-deps --manifest-path
<owned-frozen>/programs/r1-cost-probe/Cargo.toml. resolve:null is not closure.
Second only after review: full metadata, optionally --filter-platform
sbpf-solana-solana as source-justified; or changed-input correction. Record exact
scope/features/target, all compiler argv, exit/wall/RSS/swap, hashes and unchanged
source/lock. No third call, no unchanged failure retry.
6. Audit focused receipts and report actual package/index/archive requirements
versus conservative superset, config identities and compiler queries. Retain
JSON>5MB remotely by hash/size with local graph summary. Successful metadata is
not compilation, ELF identity, private sealed execution, trace closure, cache
adoption or security proof. Final Kani59/60 reserved. All existing release and
security obligations retained. Plain path-limited stage commits.

Acceptance: concrete metadata observation or demonstrated safety/input blocker;
no speculative promotion of305 missing prepared packages to build necessity.
All failures retained. Before/after theorem/premise/security statements unchanged.
