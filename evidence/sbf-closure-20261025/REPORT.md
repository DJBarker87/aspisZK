# SbfClosure bounded handoff

Branch codex/cx-sbf-closure-20261025; entry7b3ff55fffc075b5ec1e19f58dfbabf94c822863.
Criteria/design first84ac0a6e46. Only new assigned tools/evidence paths; no
merge/push, delegation, shipped/protocol/wire/feature/security changes.

Established preparation facts:
* Immutable merged SbfInputs scripts, failures, NAMESPACE and plans reviewed,
 plus prior archive/cache/source identity reports. immutable-review.json records
 exact source/dependency hashes; reuse is not a new external identity gate.
* Static frozen inspection:17 workspace/path manifests,444 lock packages,
 428 registry entries;123 prepared and305 explicitly named/checksummed missing
 from that prepared set. This is a conservative whole-lock upper bound, not proof
 all305 archives are needed. No Cargo resolver ran or extra archives copied.
 Frozen .cargo/config is an xtask alias; complete build.rs and90 source-operation
 locations recorded. Full16 default registry build.rs scripts and123 manifest
 directives inspected against the private archive-derived source hash records.
 Proc-macro2/thiserror perform compile probes; quote/serde/zerocopy query rustc;
 blake3 invokes cc on named assembly/C files and enumerates c/. They must appear
 in future descendant traces; compiler wrapper alone does not cover direct exec.
* Raw finite candidates include7978 source files, wrapper and3 metadata records,
 3479 registry records (2950 regular/529 directories),118 index entries,3828
 official platform members. Refined SbfClosure-inputs shards exclude the3
 metadata records. They remain PARTIAL candidates: index modes and private
 platform association absent. No actual private tool/rootfs was constructed.
* New2592 native/Python package path records include libc headers/crt/libgcc,
 plus seven /usr/libexec/gcc helpers separately pinned. Forty-five recursively
 inspected static ELF objects have no unresolved DT_NEEDED sonames under the
 explicit candidate search policy. No ldd/target/compiler execution; dlopen,
 native search/linker-script and actual selected file closure remain open.
* Correct SDK root found from immutable link evidence, but scan stopped at the
 external criterion link /home/dombarker/.cache/solana/v2.3.3/criterion. Its target
 was not entered/copied. No complete SDK set claimed or unchanged retry.

Literal helper/trace claims are deliberately narrow. IMPLEMENTATION.md details
actual code, unprobed Linux syscall/race/FD/capability issues and pending work.
Setup only proposes ONE tiny Python probe; empty approved manifest, no execution
CLI, actual GO schema integration explicitly denied. No boolean trusted-producer
premise substitutes for actual GO. Public file-copy/root-owned-sealing design
addresses why RO binds alone cannot exclude same-uid writers; its actual race
and syscall behavior remains unproved. Trace accepts a bounded raw syntax subset,
tracks copied process/cwd/fd/exec state and rejects unknown/unsealed/lost inputs.
It is not a full strace/Cargo parser, immutable-seal producer or fingerprint/cache
join. Both deliverable2 executable readiness and full deliverable3 remain OPEN.

Validation:39 synthetic checks exit0,0.007346931s,21446656B peak,swap0.
First Linux inventory failed on overly broad TOML path traversal; retained;
changed dependency-table scan exit0,0.438813886s,55459840B peak,swap0.
Static runtime/package analysis exit1 overall because inventory failed,9.259225546s,
52536KiB peak,swap0; its independent runtime results retained, not rerun.
Registry/native inventory exit0,0.133408120s,22528KiB peak,swap0.
SDK focused failure exit1,0.051285085s,18128KiB peak,swap0.
One focused preparation audit562 checks exit0,4.941052258s,37996KiB peak,swap0,
source39e8e4d3bc44dceb0410a19956f5bbd52149d75f. Full N/A axioms,
interpreter/helper/dependency pins, reconstructed exact -c argv and limitations
in SbfClosure-audit.json. Linux Python bounded512MiB AS. RSS is per-process,
not cgroup aggregate. Local memory setters failed before work; missing isolated
metrics stated explicitly, not fabricated. No unchanged resource failure rerun.

SbfClosure-future-plan.json normalizes stale inherited narrative after audit;
finalize-before/after compare exact behavior-bearing fields unchanged. Shell
normalization metrics/hashes retained separately. Explicit proposed host opt3
build override confirmed from official pinned Cargo1.89 reference and source;
optimization.md gives precedence and exact before/after environment. It is a
build-environment parameter change needing manager review, even with fixed ELF
pins. No heavy opt0 comparison. All3 fixed hashes and generated circle_tables.rs
identity remain mandatory; any mismatch retains evidence and STOPs adoption.
The frozen4bb capture is not a later unmerged prover-candidate identity gate.

Coordination: exact16979 launcher/start checked; no host access until gone and
codex-exit0 terminal marker plus immutable160e8876b6 report read. ResourceAdmit-v2
DENY, no scope/actualGO/marker, allocation2/2 exhausted: reused report only.
Preparatory reservation observations were below55GiB (first26172456960B plus
512MiB); not prospective/actual build admission. Registry-only public-finish
reused that recent reservation observation rather than acquiring its own; no
build/scope ran. Subsequent SDK/audit checked fresh reservations.

Transport omissions: earlier helper command fields used descriptive placeholders;
audit binds exact committed helper bytes/revisions to reconstructed -c argv.
Separate SSH/curl/export wall/RSS/swap unavailable; authoritative tool command
transcripts exist, no invented transport metrics. Host interpreter pin freshly
recorded initially, reused without per-operation revalidation; not full per-call
DSO closure. Original export tar18674176B SHA
fbbad06f2e4290b70ebcb6ebd80c826242b3634e25ca684bda0b102ae8f64f94;
audit export9441280B SHA
80f273f4cbbf23aaa33affa8c77550e7da479faa46545397f9a9bb2b97142f5b.
Only own temporary transport tars removed; no binary committed. Each derived
JSON<5MB, sharded finite lists. Audit input included incidental zero-byte own
stdout-tar destination; it is a transport artifact, not an input identity gate.

Before=after all theorem statements, premises and security contract. No new
cryptographic trust or premise discharge. No keys created/read/copied/deleted;
no RPC/wallet/chain. All Lean/Kani/Rust/compiler/Cargo/Charon/Aeneas/backend/ELF/
consumer/scope/frozen-manifest budgets0. Native/Std/P7/source-model/extraction/
memory-effect/final joins retained OPEN. BOTH SECURITY TARGETS NOT YET ESTABLISHED.

Next manager deliverable: review concrete helper/race/GO integration and resolve
SDK allowlist boundary, complete sealed public runtime and missing metadata
selection; then authorize ONE tiny privileged probe. Offline Cargo resolution and
bounded cold default→devnet/Pool capture need separate authorization, allocation
and fresh actual GO. No build or privileged probe permission is inferred here.
