# PCH round-2 handoff

Branch: codex/pc-reach1-20261110. No push. Target not yet established.

## Result

Stage 1 is admitted under the corrected (c-g) authority. Solana platform-tools
rustc 1.89.0-dev, sha256 d95c95b68e321ad76634e1fd26b0a7c20ccdbae9ad9ca733f3ae2f2b4a0b6002,
target sbpf-solana-solana, frozen Pool b936275465600469312d1f058cdc91ea2a11f3dc,
crates and lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
PCH_B003 reproduces ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc
using freshly re-emitted B002 core/statement objects. B001 plus corrected A003
postprocessing also reproduces the pin with copied retained objects. B006's
source-span diagnostic build reproduces the pin again. B005/B006 preserve their
respective baseline codegen definition symbol sets. See PCH_AUTHORITY.json,
PCH_B003_BUILD.json, PCH_B002_DEPENDENCIES.json and PCH_B005/B006_DUMP.json.
The round-1 compiler contradiction is resolved by the explicit lead correction;
its historical commits 62cb716c9bc and 11ae2cd6ec2 remain retained.

Stage 2 is PARTIAL. PCH_GRAPH.json.xz is a conservative compiler-instance
supergraph, with 87,358 nodes, 285,351 edges, 6,392 printed mono items and
78,743 MIR sites. Resolved LLVM references use exact mangled-symbol identities.
Generic MIR templates are not falsely identified with instantiated callers.
Unresolved indirect/external/handler edges conservatively include every candidate.
All 278 rows therefore remain UNRESOLVED. LLVM diagnostic paths never become
resolved source-instance witnesses. No exclusion is proposed. PCH_REMAINING.md
lists the exact remaining association for every member. PCH_DIFF_PCB_REACH.md
explains all 71 differences from PCB's source-graph assessments. Handler and tag
review is recorded separately; no cfg-disabled row is excluded. The 119 shared
observations are in PCH_SHARED_FOR_STREAM_A.json and change no Stream A status.

Stage 3's evidence-integrity validator passes. A009 is the baseline; A010–A014
reject all five required mutations, including direct/function-pointer/vtable edge
deletions with the superficial edge count repaired. It independently re-reads raw
compiler evidence for completeness. The validator does not establish the missing
resolved MIR association or certify any exclusion. See PCH_VALIDATION.json.

Stage 4's delta is empty. Pool rows CLOSED: 39 of 278 new
(A 39 / B 0 / C 0 / D 0); EXCLUDED 0 (unreachable in the deployed build; not closed);
OPEN 239; target not yet established. The 39 closures are inherited from PCE plus
PCG, without a proof-gate replay here. No live PCD_/PCF_ row changes status;
PCH_LIVE_ROWS.json records their verdicts only. No new theorem, Kani pass,
source/model refinement, trust item or cryptographic premise discharge is claimed.
#print axioms is N/A for every attempt; zero Lean and zero Kani scopes.

## Resources, failures and reproducibility

Own cache: /home/dombarker/project-offloads/codex-pc-reach1-cache-20261110.
Every retained object is copied and hashed, never hardlinked or written in place.
B001/B003 input manifests record all copied dependency hashes and frozen payload
hashes; B002 records the copied generated core table. Frozen Cargo.lock remains
5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.
Compiler cfg per project crate and the retained per-package resolved feature list
are recorded; metadata output is not confused with actual SBF compiler cfg.
No Aeneas library objects or LEAN_PATH are used by this job.

All scopes use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64.
Admission requires both exit 0 and allowed:true; refusals wait and retry. Disk
preflight requires 40 GB free before each scope. Exact argv, source revision/hash,
exit and available wall/RSS/swap metrics are in PCH_ATTEMPTS.jsonl and raw time
files. Deliberately stopped scopes may lack completed time output and receive no
success credit. Caches are retained and no key/account/fund is created or changed.

B004 was mistakenly overlapped with A006. Its own scope was immediately stopped,
gets no evidence credit and consumes a build slot. The client now has an exclusive
own-job guard. A006 was then voluntarily stopped at observed RSS 6,388,064 KiB to
split serialization. A007 stores raw-artifact locations and hashes, streams the
compressed graph, and completes at 600,280 KiB peak RSS. No cap was raised and no
timeout or memory-killed shape was rerun unchanged. B001/A002's wrong ELF filename,
A004's build.rs association, A005's unqualified MIR header, and A008's external
symbol/declaration hash distinction are retained own-input/validator repairs.

No shipped source, root/session-A/sibling worktree, shared host infrastructure or
other job cache was modified. No cache was deleted. No file over 20 MB, ELF,
compiled object or key is committed. Large textual evidence is compressed with
uncompressed SHA-256 sidecars. The final budget/accounting audit supplements this
handoff; each completed stage is committed separately.

## Next concrete deliverable

A compiler-backed generic-template-to-instance association, including substitutions,
all indirect type-compatible targets, vtable/drop/inlined edges and complete
panic/abort/allocator closure, bound to this exact ELF. Only then can codegen absence
support a candidate exclusion. The current universal unknown edges cannot do so.

## Final disposition

All round-2 slots are consumed: 6/6 build scopes, 19/19 script/audit scopes, zero Kani/Lean; see PCH_BUDGET.json. A015 source-span census, A016 deployed root/tag review, A017 frozen input/features audit, A018 three extra corruption controls, A019 accounting and A020 supplemental artifact audit all exit 0. The adopted validator is the exact A010–A014 source, whose validate() AST equals the A009 passing baseline. A018 ran three extra controls, not the locally edited four-control/mandatory-retest plan. The mutable post-run client source hash for A018 was corrected from its immutable upload snapshot, and the erroneous hash is preserved (PCH-F4). The later validator/audit strengthening is retained as uncredited; active scripts are restored to the tested versions. No claim relies on that strengthening.

PCH_FINAL_CHECK.json records local packaging/hygiene only, not another proof or host scope. All slots, including deliberately stopped/error scopes, are charged. No scope is rerun unchanged after a timeout or memory kill. No exclusion is admitted and every remaining member still needs the exact instance/handler association listed in PCH_REMAINING.md.
