# KNH isolated Kani evaluation

**Recommendation: do not adopt Kani0.68.0 for the composition medium.** It
checks the two minimal loop forms, but still cannot generate verified stubs
for slice/Vec returns, still exhibits K-1 false passes, and still exhibits
K-2 module-name-sensitive verdicts. The full55-configuration copy replay and
part of the pinned-version comparison are **incomplete**. No proof obligation
receives credit; no adoption, trust removal, or deployed security result is claimed.

Branch: `codex/cx-kani-sandbox-20261028`. Only this evidence directory changed.
Frozen release source remains `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`;
headline remains `AspisR1.RPx_Deployed.deployed`. Privacy,100-bit per-attempt
soundness and the two-transaction design are unchanged. Target not yet established.

## Installation and source pins

Candidate: [Kani0.68.0 published Linux bundle](https://github.com/model-checking/kani/releases/download/kani-0.68.0/kani-0.68.0-x86_64-unknown-linux-gnu.tar.gz),
CBMC6.11.0, Rust `nightly-2026-08-21-x86_64-unknown-linux-gnu`.
Bundle SHA256:
`32e2b484d73ede0bbf64a2cf0879c4259422497d8aec4ee67d448de9ae7843d3`.
The release API digest matched. `KNH_RELEASE.json`, `KNH_INSTALL.json`,
`KNH_INSTALL_FILES.json` and `KNH_TOOLCHAIN_PROVENANCE.json` record version,
URLs, archive/component hashes and every279 installed regular-file hash.
The corrected Rust manifest URL is in KNH_INSTALL.json; the exact original
installer source is retained as KNH_INSTALL_source.py.txt.

Private installation:
`/home/dombarker/project-offloads/codex-cx-kani-sandbox-20261028/KNH_install`.
Its toolchain symlink resolves inside that directory. Command-local PATH changes
never replace the pinned installation or edit its PATH entries. Pinned0.67.0 /
CBMC6.8.0 binary hashes match KNH_PINNED_BEFORE.json, the earlier KNC cleanup pins,
and KNH_CLEANUP.json. The private installation is retained and unchanged.

## (a) Verified return stubs and per-shape controls

All Result error types here are `u8`; slice inputs have length1. Vec bodies push
one arbitrary byte into capacity1. Box means `Box<u8>`, not an unsized box or
a production record. Actual production Error/guard/carrier coverage is not inferred.

| Return | Callee/body controls on0.68 | stub_verified caller | Disposition |
|---|---|---|---|
| `&[u8]` | N033 weak PASS, inverted FAIL, unlisted write FAIL; N003/N006 real callers PASS | N004 missing `Arbitrary` | unsupported |
| `Result<&[u8],u8>` | N034 weak PASS, inverted FAIL, unlisted write FAIL; N009/N012 real callers PASS | N010 missing `Arbitrary` | unsupported |
| `Vec<u8>` | N013 weak PASS, N014 inverted FAIL, N017 unlisted write FAIL; N015/N018 real callers PASS | N016 missing `Arbitrary` | unsupported |
| `Result<Vec<u8>,u8>` | N019 weak PASS, N020 inverted FAIL, N023 unlisted write FAIL; N021/N024 real callers PASS | N022 missing `Arbitrary` | unsupported |
| `Box<u8>` | N025 weak PASS, N026 inverted FAIL, N029 unlisted write FAIL; N027/N030 real callers PASS | N028 explicitly FAILS the unimplied byte assertion | narrow control packet behaves as required |

The missing-Arbitrary runs never reach the intended caller assertion: these are
compiler failures, **not** successful negative controls. Only Box has the full
three-control semantic packet. Its weak ensures is `true`, so its real caller's
byte equality must fail after substitution; N028 reports that exact failure.
N026 rejects the inverted byte postcondition; N029 rejects writing the unlisted
second array. This is machinery evaluation, never a native bridge or contract
adoption. [Upstream contracts documentation](https://model-checking.github.io/kani/crates/doc/kani/contracts/index.html)
also states that verified-stub return values require Arbitrary.

Five opt-level3 contract-body runs panic on an undeclared contract closure:
N002/N005/N007/N008/N011. Opt-level1 is still optimized and permits the replacement
checks N013 onward and N033/N034; the verbose compiler command records the actual
level. No claim is made that opt3 support was repaired. The initial N001 command
incorrectly forwarded standalone compiler arguments and failed CLI parsing;
RUSTFLAGS forwarding corrected our runner.

## (b) Loop invariants

N031 checks a `for _x in a.iter().enumerate()` loop with
`count == kani::index && count <= 4`: the positive conclusion count4 PASS,
false conclusion count3 FAIL. Same source in pinned O031 panics at
`loop_contracts.rs:394:44`. This reproduces a minimal for-loop compiler
obstruction on0.67 that0.68 gets past.

N032 checks a while loop through a borrowed record containing a slice of arbitrary
length0..4. The invariant reads `i <= borrowed.bytes.len()`, not a constant array
length. Positive `i == borrowed.bytes.len()` PASS; its negation FAIL.
O033 compiles this minimal source on0.67 but our old-version PATH error prevents
its solver run. Therefore this job establishes the positive/negative0.68 result,
not a completed same-probe0.67 semantic comparison or closure of NCP's larger
K054/K055/K066 validators. No whole-buffer native bridge is claimed.

## (c) Fidelity

**K-1 persists.** N039 selects the exact110 expected/wrong harness names from
the55-row KMX_CONFIGURATION_MAP.json. Before the larger case stalls, it completes:

| Original configuration | Correct assertion | Wrong-zero assertion |
|---|---|---|
| c049: u32[16], last512, slice-destination helper | FAIL | **PASS** |
| c052: u32[1], value1 | FAIL | **PASS** |
| c053: u32[1], value255 | FAIL | **PASS** |
| c054: u32[1], value256 | FAIL | **PASS** |
| c050, c051 | PASS | FAIL |

Each false-pass pair includes an explicit failing value assertion and a successful
false zero assertion. It is not inferred solely from process exit. This answers
whether builtin copy still loses data on the candidate: **yes on these fixtures**.
It does not establish fidelity for every buffer/type/configuration.

c023_wrong (`[u8;32]` elements,16 elements) hits the unchanged90-second CBMC limit.
The bulk driver had already advanced to c023_correct when we stopped its own driver
and solver; that mate is interrupted and excluded. N039 exits241 after SIGTERM,
wall161.669s, peak6,503,356KiB,swap0. The queue advancing before timeout review is
a process failure, not an accepted rerun policy. KNH_N039_REVIEW.json records it.
No identical timed-out harness is submitted again and no cap/timeout increases.

N040 attempts a split mitigated matrix: original bodies up to128 bytes, one-cell
logical-window diagnostics for larger configurations. These windows do **not**
prove a full-buffer frame; no Lean composition is claimed. Our split generator
omits KMX_slice_destination, causing compile failure before any solver check.
KNH_N040_source.rs.txt preserves that exact failing input. The helper is repaired
verbatim in the retained split source/generator, but no new-version run remains.
Thus the new-version mitigated matrix and the full original55-row replay are OPEN.
KNH_COPY_MATRIX.json explicitly leaves49 original rows unresolved; it does not
turn missing results into passes. The repaired old split matrix O039 also never
reaches its solver because of our PATH error below.

The replacement implementations are extracted exactly from the approved
`evidence/kani-mitig-20261028/KMX_copy_stubs.patch`, SHA256
`bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
KNH_KMX_stubs.rs.txt contains that exact KMX_stubs.rs payload. No custom copy stub
was authored. Copy-dependent passes receive no new native credit: the matching
candidate copy-mitigation controls did not finish.

**K-2 persists.** The minimal body preserves NBZ helper/global/harness names,
namespace structure and the actual Phase/Observer definitions. No frozen verifier
code is compiled. Only the requested experimental change differs between probes:

| Run | Experimental change |0.68 result |
|---|---|---|
| N035 | baseline, module NBZ_native | FALSE FAIL of literal None assertion |
| N036 | observer assertion changed to is_some | explicit intended FAIL |
| N037 | payload assertion changed to i>=10, with i<10 assumed | explicit intended FAIL; original None assertion also fails |
| N038 | module identifier alone changed to KNC_native | PASS, **quarantined** |

This is a new-version repetition of the direction/name sensitivity, not a fix.
The renamed pass receives no credit. No false PASS is demonstrated by these K-2
probes; K-1 independently demonstrates false passes. The minimal scratch context
is not the complete historical frozen workspace. Pinned O035/O038 fail our PATH
setup before solving, so they do not supply a fresh old-version comparison.

## Receipts, process exceptions and budget

KNH_ATTEMPTS.jsonl contains50 configured Kani invocations, plus installation and
audit receipts. **40/40 new,10/10 pinned,0 Lean.** Compiler and CLI failures count
against the budget. KNH_RESULTS.json and KNH_HARNESS_RESULTS.json distinguish
process classification from each observed property verdict. Every receipt records
exact command/target, source revision and hashes, exit, wall, peak RSS, swap and
cgroup limits. `#print axioms`: **N/A throughout; zero Lean modules/theorems**.
The invocation classification is not a closure count:

- New:14 PASS invocations,14 check-failure invocations,5 compiler panics,
  4 missing-Arbitrary errors,2 CLI/input compile errors,1 interrupted matrix.
- Pinned:4 matching missing-Arbitrary errors,1 for-loop compiler panic,
  5 own PATH failures. O028/O033/O035/O038/O039 lack the pinned bin directory
  in command-local PATH, so goto-cc cannot be found. The runner is repaired,
  but no further pinned invocation is authorized by the exhausted budget.

**Graph-process gap:** N001–N019 omit the required fresh frozen-workspace metadata
preflight. Their standalone sources have no Cargo dependencies, cfg-if/libc are
unreachable, and the copied frozen lock remains exact, but this is not compliance
with the literal per-invocation graph rule. No such historical preflight is
fabricated. N020–N040 and every pinned run use KNH_gate.py: fresh offline/locked
metadata from the existing retained KMX workspace, exact441-package/edge graph
comparison against the frozen baseline, all resolved features recorded, then the
standalone source, then unchanged hashes of both locks. That workspace is accessed
read-only; no code is compiled into its target directories. Every scratch-lock
before/after hash is `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.
The scratch sources are tool probes and receive no deployed-feature/source credit.

All launched scopes are serial and admitted with exit0 AND allowed:true, using
MemoryHigh6G,MemoryMax8G,MemorySwapMax0,TasksMax64. No cap increased; all swaps0.
Two prelaunch upload connection resets were handled by compressing our oversized
source transport; no proof had been submitted. All wrapper fixes concern our own
scripts, never reservation/launcher/shim/shared infrastructure. Source and failure
snapshots remain available; nothing was renamed to obtain proof credit.

KNH_CLEANUP.json: pinned tool hashes unchanged,279 installed regular files unchanged,
470 imported cache files unchanged, private cache and isolated installation retained,
own targets/temp removed, no own prover remains. No keys were used or removed.
No shipped-file changes, ELF rebuilds, full release replay or push occurred.
Inherited, not rebuilt: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Revalidation required before any later adoption

1. Resolve slice/Vec return generation and rerun each exact intended return/error/
   ownership shape with a proved callee, real caller, substituted caller, inverted
   ensures, unimplied assertion and modifies control. Box<u8> does not admit
   Box<[u8]>, SDK guards or production records. Repeat all evidence intended for
   use from N001–N019 under the strict graph preflight; it cannot be repaired retroactively.
2. Fix and validate K-1 and K-2 against matched native results, both directions,
   original names and name-only variants. Retain the Option<fn> quarantine and
   approved copy replacements until the lead separately rules otherwise. Complete
   the original55-row comparison; timed-out large cells need native single-window
   checks plus independently checked Lean frame/disjointness composition, not a
   larger timeout or inference from the current logical-window placeholders.
3. Repair the input/PATH setup and rerun the missing pinned comparisons. Recheck
   the original NCP for/enumerate and borrowed-record leaves, not just these small
   probes; validate the selected optimization profile, including the opt3 contract
   closure panic. Keep same-version controls and matched callee/caller domains.
4. Under a later lead adoption decision, pin all tool/sysroot/source/feature hashes,
   revalidate every proof packet whose trust depends on the changed toolchain,
   then perform one complete frozen deployed-feature vertical slice and affected
   dependency-closure audit. Native contract semantic transport remains the owner-
   approved P6/D188 trust clarification: any use is a reclassification, never removal.

Remaining members require new Kani budget/tool correction: four slice/Vec stub
families need compiler support and caller controls; larger Box/error families
need their own contracts; the full NCP loop leaves and old while comparison need
solver runs; K-1 needs the missing matrix/window checks and a future Lean frame
budget; K-2 needs an independently validated tool correction and original-context
rechecks; the19 missing preflights require replacement invocations. There is **no
Lean-only obligation authorized in this zero-Lean sandbox job**. No assumption is
discharged, added, weakened or removed, and no S2/native/security row is closed.
