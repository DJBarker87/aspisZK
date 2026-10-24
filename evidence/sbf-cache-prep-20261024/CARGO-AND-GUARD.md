# Cargo identity and pre-exec guard assessment

The newly queried pinned official SBF Cargo is1.89.0 ca74c32f0ac6d99000858dcae9b0931ef76a8f43.
Outer host Cargo1.94.1/29ea6fb6a is REUSED from entry metadata, not queried anew.
Official source URLs, hashes and selected line indices are in cargo-source-research.json.
No GPL source was copied into this repository. Failed web cache fetches at the
short SBF revision were resolved using official GitHub commit metadata, then
full-SHA raw source fetches; no package installation or compiler execution.

In ca74c32f0 util/rustc.rs317-380, compiler-query cache identity incorporates
resolved compiler and wrapper paths, length and creation/modification times,
plus applicable Rustup context. That cache identity is NOT the compilation-unit
fingerprint. fingerprint/mod.rs1562 and1637 hash actual verbose rustc version
for normal/build-script fingerprints; dependencies, target, profile, features,
source-relative path, Rustflags, config and local checks also matter. Therefore
changing general RUSTC_WRAPPER can refresh metadata queries without necessarily
rebuilding every unit; claiming either unchanged warmth or universal coldness
from that fact alone is unjustified. Full original diagnostics wrapper bytes
fa74d69e... were inspected via Git; exact metadata argv forwards to real rustc.
No fake version/fingerprint output is proposed.

build_runner/compilation_files.rs677 hashes RUSTC_WORKSPACE_WRAPPER into workspace
unit identity. Changing it is not identity-transparent. Both compiler and wrapper
relocation need actual unit/fingerprint and dep-info assessment. This inventory
contains662 fingerprint JSONs sharing rustc field10071411861207962412 and
compiler-query-cache identity11236034022870326026. Cached version answers match
the previously observed official1.89.0-dev/LLVM20.1.7 text, with unknown commit.
That agreement does not prove historical compiler bytes or provenance.

custom_build.rs331-350 constructs a direct build-script process;562-568 executes
it. The compiler wrapper is passed as an environment value to scripts at435,
not used to wrap their execution. A cached script can therefore start expensive
native compilation before ANY compiler-wrapper hook runs. The concrete
wrapper-only proposal is rejected; the counterexample is retained in guard tests.

SbfCachePrep_guard.py is an OFFLINE policy specification, not a real broker or
installation. Sixteen synthetic cases cover exact version/sysroot forwarding,
query-plus-compile argument rejection, response files, dependency AND selected
unsealed compiles, changed identity, cached scripts and shell/native children.
All build execution denies. A future broker must intercept every execve/execveat
before execution across fork/vfork/clone descendants, bind executable identity
and ordered argv/cwd/explicit environment/input closure, and deny missing/raced
identities. It must cover scripts even if Cargo considers their compiler unit
fresh. Neither actual interception nor its compatibility with Cargo is tested.
No ptrace/seccomp/security settings, wrappers, source mtimes, caches or arguments
were installed/edited to force a pass. No fallback cold build is allowed.

Dep-info includes prior cu-bound/format-adopt/stage2b/pin targets and S10 source
paths, not the recapture source. These are named provenance references only;
none of those worktrees/caches were opened. Exact source/OUT_DIR/build-script
and target-path relocation compatibility is OPEN. Current target/feature/profile
JSON values are retained in provenance.json, not equated with a frozen source
or current official tool input closure. Default→devnet changes and new diagnostics
must be assessed without pretending reused outputs are freshly emitted.
