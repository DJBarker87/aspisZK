# Proposed optimized host build scripts

Selected Cargo source commit ca74c32f0ac6d99000858dcae9b0931ef76a8f43.
Official reference config.md926–931 documents
CARGO_PROFILE_<name>_BUILD_OVERRIDE_<key>; profiles.md321–332 documents default
host opt0,435–459 build-script/proc-macro/dependency overrides and precedence.
profiles.rs440–496 actually sets host opt0 then merges build_override; UnitFor
980–1015 includes build.rs even for a target/nonhost package. This covers the
compiled aspis-core build.rs executable, not merely its build dependencies.
RunCustomBuild's special profile concerns environment, not how its executable
was compiled. A named package override can win, so effective configuration must
remain part of input closure. Frozen root release package entries specify only
overflow-checks for two different packages; root .cargo/config only an xtask alias.
Actual complete selected SDK/ancestor/config set is still unsealed.

Before: no explicit CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL.
After PROPOSED: CARGO_PROFILE_RELEASE_BUILD_OVERRIDE_OPT_LEVEL=3.
Future plan preserves all other explicit environment entries, exact original
argv/-j4/linkerthreads4/features/logicalpaths/diagnostic wrapper bytes and three
ELF pins. This is an explicit frozen build-environment parameter proposal,
requiring manager review; fixed ELF hashes do not waive that policy boundary.
All build-script/proc-macro/host-dependency fingerprints may change. Default
must be cold; devnet may share only its new validated cache, Pool stays distinct.
Do not compare by executing the heavy opt0 generator. Record newly generated
circle_tables.rs identity and every affected command/cache/output association;
require ALL3 fixed ELF hashes. Mismatch retains evidence and stops adoption,
without source/pin update. No optimized build or Cargo ran here.

Full immutable docs and implementation retained, with hashes in future audit.
URLs:
https://raw.githubusercontent.com/rust-lang/cargo/ca74c32f0ac6d99000858dcae9b0931ef76a8f43/src/doc/src/reference/config.md
https://raw.githubusercontent.com/rust-lang/cargo/ca74c32f0ac6d99000858dcae9b0931ef76a8f43/src/doc/src/reference/profiles.md
https://raw.githubusercontent.com/rust-lang/cargo/ca74c32f0ac6d99000858dcae9b0931ef76a8f43/src/cargo/core/profiles.rs
Acquisition: three curl --fail --location --max-time30 --max-filesize1000000
operations exit0. Each combined tool transport also included following commands,
so isolated curl RSS/swap/wall were not measured; do not invent these metrics.
Web fetch first returned cache-miss; direct official immutable fetch succeeded.
