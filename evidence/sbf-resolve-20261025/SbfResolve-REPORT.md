# SbfResolve handoff

Assigned branch codex/cx-sbf-resolve-20261025, entry65c4082110.
Criteria/plan committed53bf861f4a before operations. Only assigned new paths
changed; no merge/push, delegation or shipped source changes.

Actual frozen4bb metadata resolution is now observed, rather than a speculative
305-package blocker. Exactly TWO Cargo CLI invocations used; no slots remain.
Selected official Cargo1.89 ca74c32f0 and rustc bytes were addressed directly,
not through rustup. Primary source assessment precedes both calls.

* Query1 `metadata --offline --locked --format-version 1 --no-deps
  --manifest-path <owned-frozen>/programs/r1-cost-probe/Cargo.toml` exited0,
  returned13 workspace packages and resolve:null; no rustc call.0.060775751s,
  helper24912KiB peak, child24912KiB peak, sampled aggregate46206976B,swap0.
* Query2 removes --no-deps, adds `--filter-platform sbpf-solana-solana`:
  exit0,357 graph nodes/packages including344 registry packages. Whole workspace,
  default features, dev dependencies and host metadata discovery; not a package-
  only selected build.0.543161591s; helper35240KiB, child103556KiB peak,
  sampled aggregate132997120B,swap0. Complete collector wall0.991813466s.
* Exactly3 rustc calls: -vV, empty-stdin host print discovery, and SBF print
  discovery. Exact argv in raw-compiler-queries.jsonl and raw trace. All are
  print-only; no crate compilation, build.rs or proc-macro execution. Source route
  exclusion supplies that conclusion; compiler wrapper alone would not exclude
  cached build-script execution. Per-rustc wall/RSS were not isolated; grouped
  query metrics and raw exit/wait records retained. Target tree remains empty.

Concrete sets in SbfResolve-sets.json:394 index files opened;371 package archive/
source sets opened;428 archive presence paths observed. Returned registry graph344,
including221 beyond initial123. Root reachability in the workspace-unified graph
is178 packages/174 registry, including51 beyond initial123; this is not an
independently feature-resolved root or compilation-unit result. Prepared428 is a
conservative locked superset:84 absent from returned graph,57 without source-open
observation. No minimal-cache counterfactual was run;305 is NOT selected-build
necessity. Lexical trace census is not SbfClosure trace/parser/cache closure.

New own0700 stage is /home/dombarker/project-offloads/
codex-cx-sbf-recapture-20261024/SbfResolve-20261025-v1. Reviewed123 view/118 indices
privately copied; additional305 archive data and remaining indices copied only
from exact PUBLIC .crate/index cache, locked version/checksum validated. No global
unpacked source/ICE logs, credentials, live worktrees or user/task keys accessed.
Public test/signing fixtures and packaged Windows import libraries retain exact
archive association. No downloads/installs/adoption. Safe file/path/type/mode/
duplicate/size checks, no mutable-donor hardlinks. Official completion markers
remain distinguished from archive checksums/fingerprints.

Private manifest19714 regular files/508827855B,428 packages/markers,394 indices;
6304167-byte JSONL remains remote, SHA256
5cc3aadc508d3cd11dc6182228bbf9cf296d64f1992903e70d5348225c23c276.
Local graph/raw JSON each<5MB. Prior7978-file/104193141B source and3828-member
platform archive equality reused explicitly; no unchanged full replay.19 reviewed
manifest/config/lock pins freshly checked. Lock remains5782e6a3...22ef.

Clean /tmp/SbfResolve-20261025-v1 cwd config candidates absent; only own21-byte
CARGO_HOME/config.toml opened (SHAe3987c0b...48a7e); public registry endpoint config
separately pinned. Explicit clean environment/HOME/settings/target/cache retained.
No original S10 logical-path environment equality inferred.11 tool/driver/loader/
DSO paths before/after unchanged; final34 named seals additionally confirm guard,
control, config and source pins. Full Python stdlib/pyc/dynamic runtime seal remains
open; same-uid0700 is not immutable execution. Raw trace records negative probes,
shared threads and unfinished/resumed calls; no full trace PASS claimed.

Fresh metadata/data admission observations: populated finite reservations
26172456960B (<55GiB with512MiB allowance), control availability>7GiB. Ordinary
metadata sampled RSS guard512MiB, deadlines90s,32MiB output bounds; inherited
AS/DATA unlimited and not changed. No scope creation/build GO. Final export/post
reads reused recent query admission rather than collecting new reservations.

Four changed-input public filename-policy failures and one collector serialization
failure retained in FAILURES.md, exact source snapshots and receipts. No resource
failure/retry. Final universe exit0,3.543492466s,67472KiB process/
70303744B aggregate,swap0,zero download attempts. Guard34 checks; fixture policy9.
Focused offline audit8362 checks exit0,0.093057417s,47185920B peak,swap0,
source8508b53c51. Final post seals exit0,0.158794388s,17076KiB,swap0,
sourceb122a4e704. Exact argv/revisions/helper/dependency/input/output hashes and N/A
axioms retained in receipts. Some early research/export transport failure metrics
are unavailable as documented, not reconstructed.

Reporting corrections: universe origin=reused123 means already present on that
continuation, including partial earlier additions; authoritative initial123 flags
are reconstructed from immutable packages.json. Staged helper file is the initial
reference, not later executed -c helper; audit matches actual -c bytes to each
source revision. These distinctions are explicit in sets.json.

Before=after theorem statements/premises/security contract; no new trust or premise
discharge. Zero Lean/Kani/build/codegen/Charon/Aeneas/backend/ELF/privilege/namespace/
mount/sudo/key/RPC operations; final Kani59/60 reserved. Fixed ELF default
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
unchanged, not rebuilt. Future opt3 build-script override remains manager-reviewed
proposal with all3 ELF/generated-table byte gates mandatory.

Next deliverable: lead review of this concrete metadata packet, then separately
allocated root-owned sealed setup/actual GO/SDK external-link policy, syscall/FD/
stdout/trace/cache and artifact gates. Metadata success does not close build,
ELF/native/Std/P7/source-model/extraction/effect/security obligations or adopt a
later unmerged prover candidate. BOTH TARGETS NOT ESTABLISHED.
