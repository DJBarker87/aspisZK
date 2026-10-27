# Integrated prover-candidate sibling

Branch **codex/pv-integ2-20261027**, base **0c9dc9a4cc**. Integration task completed; **target not yet established**. No existing implementation or Lean source was edited beyond the requested merges. The only new Lean file is the requested command-only audit in this evidence directory. No push occurred.

All nine requested branches merged cleanly, in order, with one `git merge --no-ff` commit each:

| Branch suffix | Merge commit |
|---|---|
| pv-cb3-20261026 | 43d7b8d6f8 |
| pv-cb9-20261027 | ebfa11efe0 |
| pv-cbmid-20261027 | 9ea1fbbffa |
| pv-op134-20261027 | fc53a00c75 |
| pv-cblib-20261027 | e50a3d14de |
| pv-join-20261026 | 6360ebd14d |
| pv-l2b-20261027 | 14efd77c15 |
| pv-n7-20261027 | 7d3852b008 |
| pv-route2-20261027 | 5465d05960 |

No merge was aborted and no conflict was resolved. [merges.jsonl](merges.jsonl) pins both parents and each branch tip; [CONFLICTS.md](CONFLICTS.md) records the empty conflict set. All four excluded branch tips remain outside this sibling's ancestry at the recorded check; see [excluded-branches.json](excluded-branches.json). Full imported `git log --oneline 0c9dc9a4cc..HEAD` history and first-parent stage history are retained in [imported-history.txt](imported-history.txt) and [stage-commits.txt](stage-commits.txt), up to the final report stage.

The only crates/programs change is an appended section of `crates/aspis-r1-cost-probe/src/host_commitment.rs`: three `#[cfg(kani)]` modules, with the production prefix byte-identical. The parent module is also behind `feature="prover"`. No programs/ or scripts/ file changed. [SOURCE-GATES.md](SOURCE-GATES.md), [crates.diff](crates.diff), and [source-gate-check.json](source-gate-check.json) show the exact gates and release dependency features. Every tools/ addition is listed in [changed-files.txt](changed-files.txt). Those standalone proof/reference tools are outside release builds, not literally inside cfg(kani); that distinction is explicit rather than asserted falsely.

All three ELFs were rebuilt sequentially from integrated source revision **c9fd6b99fadb8259cdabbeadf1a852e71245f3cf**, with optimized SBF compilation under MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Exact inputs are pinned by [build-inputs.json](build-inputs.json). All pins match:

| ELF | SHA-256 | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| default | f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 | 0 | 51.233 | 683640 | 0 |
| devnet | 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 | 0 | 40.804 | 683220 | 0 |
| Pool | 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548 | 0 | 61.444 | 680060 | 0 |

[elf-gate.json](elf-gate.json) and native-receipts/ retain commands, features, source revision, admission, cgroup limits/peak, exit, time, RSS, swap and N/A Lean-axioms classification. Three devnet admission refusals launched no compiler. One retry was about eight seconds early; no scope started, and the subsequent timestamp guard enforced the full cooldown. The inherited native compiler PATH and explicit shim-path correction are also recorded in [PROCESS.md](PROCESS.md). No cap or admission check was weakened.

The merges add distinct Lean files; no existing Lean source/import was changed. We reused **816 PV objects** and rebuilt **25 missing objects**, in dependency order: seven L2B helpers and eighteen inherited CB helpers. Every recheck passed, IDs **54300–54324**, zero swaps, maximum process RSS **4,323,992 KiB**. No unchanged full regression was run. [cache-reuse.json](cache-reuse.json), [publication-rechecks.json](publication-rechecks.json), and [focused-summary.json](focused-summary.json) record reuse/missing-object reasons; lean-receipts/ records each target, source/dependency hashes, source revision, exit, wall, RSS, swap and full axioms output. Shared env-J sources were never written. Existing h'-compliant private-root launcher/cache procedure was reused; shared source resolution uses the rebuild record, not the older source-pin table.

The one combined final module [PV_Integ2_CombinedAudit.lean](PV_Integ2_CombinedAudit.lean) checks **533 publication targets across 223 direct imports**, including CB, CB3, CBM, op134, CBL's additive publication, the aggregate join caller, L2B and op223. Command-only historical audit modules are inlined instead of requesting absent command-only objects. All 533 reports use only subsets of **propext, Classical.choice, Quot.sound**; no unsupported axiom. Target coverage and all receipts pass [validate.py](validate.py).

| Final target | Attempt | Source revision | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---|---:|---|---:|---:|
| PV_Integ2_CombinedAudit | 54597 | 5a31e1819d | 0 | 0:02.59 | 4378296 | 0 |

Exact final source hash, dependency fingerprint and full axiom output are in [lean-receipts/54597/receipt.json](lean-receipts/54597/receipt.json), dependencies.json and out.log. **26/100 Lean attempts charged, 0/0 Kani**; no Lean refusal or failure. IDs never reused. Reserved audit IDs 54598–54599 remain unused; [TALLY.json](TALLY.json) is authoritative.

[ROWS.md](ROWS.md) gives each bundle's reported row scope, overlap and retained obligations. [consumer-paths.json](consumer-paths.json) supplies source-import paths and explicit missing paths. The alternate aggregate/public callers import CB/CB3 source laws, but these publications are not imported by the canonical deployed headline. CBL/CBM/op134/L2B remain separate support publications. `PV_Op223_V164.refinement` imports its source proof and supplies P_source_p6 while retaining reservation and P_proof_bytes. Integration itself removes **zero endpoint premises**, adds no trust field, and changes no quantifier, simulator, observer, failure event or bound.

This is focused publication compatibility and axioms evidence, not a fresh coherent replay of the complete deployed endpoint. Four unresolved historical source-map names and 27 inherited modules whose shared source snapshots are absent are explicitly retained in the formal/cache inventories; their existing objects are reused, not silently re-sourced. E1/E2, native/world source association, real RunJoin, OS-failure witness independence, proof bytes, L1/L2/L3 including substantive V371, client adoption, and final endpoint closure/release binding remain. T remains exactly entropy_law, entropy_kernel, observation.

Host directory: `/home/dombarker/project-offloads/codex-pv-integ2-20261027/`. [cleanup.json](cleanup.json) records removal of only this job's rebuildable native/private-object caches after receipts and hashes were retained. All three generated SBF keys remain at mode 0600, with public identities in [key-retention.json](key-retention.json); no wallet/key was deleted and no transaction was sent. No binary, ELF, key or .olean is committed.

Next deliverable: lead review/adoption of this pinned sibling, then compose the published source dictionaries at the same concrete extracted caller and discharge that caller's proof-byte/reservation/native-world associations before the coherent deployed endpoint replay. No security target is declared established by this integration.
