# SBFIDENTITY result

Historical S10 re-pin3 compiler/sysroot identity is **not recovered**. New work
establishes a current installed content manifest and exact official source
correspondence at the declared Rust fork commit, plus a concrete proposed next
capture gate. No historical go capture, official archive-content comparison,
new ELF identity gate, native semantics law or security closure is claimed.
Both deployed security targets remain **not yet established**.

## Current capture

The selected `.rustup/toolchains/1.89.0-sbpf-solana-v1.52` is a two-link chain:
Solana3.1.13's global SDK dependencies → global `.cache/solana/v1.52/platform-tools`.
All links were resolved before target reads; no private lookup was followed or
blocked. `rustc -vV`/`--print sysroot` and direct configured host cargo/rustc `-V`
were metadata queries only. The SBF compiler says commit/date **unknown**,
release1.89.0-dev, LLVM20.1.7. Paths/versions were not used as content identity.

| Current file | SHA-256 |
|---|---|
| rustc | d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002 |
| librustc_driver | 3b1ea655c8f47c30490b07740a872974e34747ab7ba39c56ae20fba044bd0dae |
| sbpf core archive | a1f52278d174e0741f3b6269254cad81b6a1e2ecb1a7ce7f2460429d28dae09b |
| sbpf alloc archive | 6a7f83ac4e22637de88c8b8919a0ac59c54b8c433a233eb435298d2aa72b9531 |

`current-content.json` pins2,230 files with sizes/modes/mtimes; it includes all
selected-target archives and full packaged rust-src. `current-source-tree.json`
adds complete Git blob IDs and a bounded released-S10 metadata assessment.
`current-drivers.json` pins build-sbf, the actual small gcc-ld shim, rust-lld,
rustup proxy, resolved host tools and global selection settings. These are
**current** observations, not proof of historical selection or a complete
future execution-input manifest. Tools and source must be freshly captured at go.

The installed version.md declares Rust
`790f1537507dbdb0da320fbb3b1c1eca3b33c474`, cargo
`ca74c32f0ac6d99000858dcae9b0931ef76a8f43`, newlib
`f0f8003daa3f71a1a3e2f067f8d5bb46e2756514`. Exact official Rust commit metadata
and trees were fetched; its LLVM gitlink is the observed
`78496716176191b2dfb728e5e38501812e7467db`.

Complete core284/alloc72 file sets, Git blob IDs and executable modes agree
with that official commit: no missing/extra/mismatching file. All1,785 direct
library blobs agree;409 additional packaged files belong to the three gitlink
submodules and are **not** claimed separately verified upstream. Nine complete
files (including Cargo.lock, allocator, RawVec, Vec, array/clone/layout sources)
also have direct official-raw-byte SHA-256 comparisons, all equal. Thus the
complete-tree result is Git-content-hash/mode correspondence; the nine-file
result independently compares SHA-256. The initial progress shorthand
“byte-for-byte” should be read with this exact evidence distinction. No source
presence or official declaration is promoted to proof of what compiled binaries.

Primary official references, pinned locally with HTTP/command/hash receipts:
[platform-tools v1.52 release](https://github.com/anza-xyz/platform-tools/releases/tag/v1.52),
[platform build commit](https://github.com/anza-xyz/platform-tools/blob/e3ebfccfe63ba936dd6951ede390496c6bc2f296/build.sh),
[Rust commit](https://github.com/anza-xyz/rust/commit/790f1537507dbdb0da320fbb3b1c1eca3b33c474).
The official Linux x86_64 archive digest/size is retained in the plan; no large
archive was present at the inspected v1.52 root or downloaded, so complete
installed-versus-official-archive equality remains open.

## Historical evidence assessment and assumptions

`immutable-assessment.json` pins28 immutable inputs at
`3e9998bbfc828c6e9455cc45a846dcd0f5372710`. Its S10 source manifest has7,978
records, revision4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 and SHA-256
`a84a528cfc4b294c603fe5381343cdaf9df0547467bcc94e61a67e5111adb9d1`;
the retained host manifest matches. Historical raw receipt sourceb2727acd is
stale and not substituted for the manifest. Read-only older S2-trust receipts
bind rustc/core/std hashes matching today's bytes; parser-era metadata pins
build-sbf and gcc-ld too. Those receipts concern different source revisions /
earlier artifact pins, lack a full alloc/driver/source pre-go join for re-pin3,
and are **reused historical observations**, not a new identity gate. A focused
tracked S10 metadata search returned no exact compiler/core/alloc/commit match;
this is a bounded search, not proof that no custodian has another receipt.
Only released snapshot top-level metadata was inspected; donor target caches
were neither entered nor mutated. No session-A candidate source was used.

Complete `R1FinalSoundness.lean` and P7 reacceptance text were inspected as
immutable objects. The hidden structures intentionally contain arbitrary
proposition slots, not a source-to-SBF semantics definition. Before = after:
`BoundaryStatements.P7 : Prop`; `BoundaryEvidence.h_P7 : s.P7`.
`final_soundness` still takes `s`, `BoundaryEvidence s`, and all its concrete
source/experiment/transport obligations. No theorem statement changed, no
premise was discharged/added/repackaged, and no output equivalence was hidden
in a new structure. P7 retains exactly reviewed-source/locked-dependency to
selected-ELF compiler correctness; byte reproduction only supports identity.
R22 arithmetic correspondence and native memory/ordered fault/oracle semantics
remain separate obligations. No new trust assumption or adoption was made.

## Next deliverable and validation

`RECAPTURE.md` and `recapture-plan.json` specify a fresh own stage, precise
three-mode commands/features/IDs/outputs, wrapper pin, source/lock pins, named
warm-cache donors and read-only export assessment, official archive criterion,
pre/go/post manifests, fresh diagnostics, unchanged strict resource admissions,
per-mode predecessor wall/RSS/cgroup/swap and exact expected ELF pins. It is a
proposal only. Lead authorization, custodian-approved pinned cache export,
matching official archive availability, and approved strict admission runner
are explicit launch prerequisites; failure cannot trigger an install, broad
bootstrap, alternate tools, forced ELF, new trust, or a larger-cap retry.
A pass would establish a **new** captured association under P7, not historical
identity by decree or source-to-native security.

New validation: four host read/hash captures (all exit0; host walls0.322s,
0.848s,0.247s,0.185s for global/content/source-tree/drivers respectively; exact
unrounded values and per-process/children RSS in receipts), primary metadata /
small-source fetches, immutable receipt assessment, source comparison, plan
construction and one final focused offline integrity audit. All recorded swap0;
metadata peak far below8GiB. See the machine receipts for authoritative values.
No scope/build reservation was created: actual scope/admission/time-window
checks are N/A to these small metadata operations. Future build caps stay6G/8G,
noSwap/Tasks64, strict finite<55GiB plus existing exclusive accounting/control/
MemAvailable gates; proposed slab credit is not adopted.

Unchanged Port24's56 outputs/121 checks and S10 build/proof/runtime receipts are
reused only; their gates were not repeated. No proof/build failure was retried.
Rejected approaches retained: version/path equals identity; current hashes as
historical go; old receipt as new all-three gate; official source declaration
as compiled-source proof; host/Kani sources as SBF sources. Inspection queries
with no match retain exit1 as search-not-found, not a failed build. No theorem
or allocator/body/Vec inventory was regenerated.

Budgets: compiler BUILD0, Lean0, Kani0, extraction0, Rust/arithmetic0, ELF gate0,
full frozen manifest0, backend0. #print axioms is N/A for every new result;
no theorem or axiom was added. All changes are new files under the two allowed
job directories. No merge/push, key/service/cache/chain mutation or shipped
source/protocol/wire/feature/security-contract change.
