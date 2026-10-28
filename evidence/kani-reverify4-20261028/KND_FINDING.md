# KND checkpoint append finding

**0 original rows CONFIRMED, 0 FAILED, 9 OPEN. Checkpoint/append leaf credit stays SUSPENDED; prior checkpoint restoration remains 3/12.**

The fixed 64-weight writer has 116 distinct transitions, all at capacity 1768. Budget 90 permits at most 45 positive/control pairs. 43/45 selected pairs earn transition credit; 73/116 scheduled transitions remain uncredited. No timeout earns credit.

## Schedule theorem and scope

`KND_Schedule.exact_schedule` and `data_independent` prove the source-order metadata model is fixed. `append_count`, `final_length`, and `no_growth` establish 116 appends, 1768 bytes and no growth. [Schedule](KND_SCHEDULE.json), [frozen source excerpt](KND_writer.txt), [first compile and axioms](KND_L001/receipt.json).

Layout: magic 8, header 8, proof/public/state/two roots 32 each, four wide 32, rho 16, 22 query words 4, 10 semantic scalars 16, four z coordinates 16, claim/rhs 32, power 16, 64 weights 16, checksum 32. Weights span 712..1736. Appended values do not control the fixed loops.

The model is a manual source transcription, not an extracted Rust execution-equivalence proof. The 1768 path requires variant final_len=64 and weights.len=64; arbitrary calls to the public checkpoint API do not have that guarantee. The writer reserves 1768, whereas earlier arbitrary-prefix and checksum cuts use cap=len or cap 1736 with growth to 3472. Reachable lengths do not imply universally quantified arbitrary-prefix assertions. [Scope analysis](KND_SCOPE.md).

## Concrete transition evidence

All twelve size 32 and twenty-two size 4 writer transitions were selected, followed by weight 53..63. Each harness fixes len/cap/size, keeps initial/appended bytes arbitrary, and covers the entire live result (one arbitrary observed index for pairs 1..33; every concrete index for pairs 34..45). Constructor length/capacity and resulting prefix, appended bytes, length/capacity are asserted. Matched controls differ only by XOR1 of the expected byte; the name stays KND_transition. No copy stub was written. Exact KMX definitions are reused. KND_K071..K090 initialize through Vec::from(array 1768) and concrete truncate; earlier attempts use with_capacity plus KMX prefix initialization. Array setup initializes spare bytes, so no additional uninitialized-spare refinement credit is inferred. [Constructor change](KND_CONSTRUCTOR_CHANGE.json). The observation change was made only for previously unrun transitions; KND_K066 was recovered read-only after its host process completed. [Change receipt](KND_OBSERVATION_CHANGE.json). New function-pointer/Option<fn> quarantine list: **empty**.

Kani statuses: {'PASS': 43, 'COUNTEREXAMPLE': 43, 'TIMEOUT': 4}. Negative-control counterexamples are expected control results, not original-property failures. [Pairs](KND_PAIRS.json), [matching audit](KND_PAIR_AUDIT.json), [uncredited triples](KND_REMAINING_RUNTIME.json).

## Per-row decisions

| Original row | Decision and remaining obligation |
|---|---|
| LPm_K003 | **OPEN.** All 64 selected references and scalar association required; only eleven raw-byte weight transitions selected. Original cap=len differs from writer cap1768. |
| LPm_K004 | **OPEN.** Original arbitrary-length/capacity heap relation is broader than fixed writer reachability. |
| LPm_K005 | **OPEN.** Original arbitrary-length/capacity heap relation is broader than fixed writer reachability. |
| LPi_K012 | **OPEN.** Original arbitrary-length/capacity heap relation is broader than fixed writer reachability. |
| LPi_K013 | **OPEN.** Original arbitrary-length/capacity heap relation is broader than fixed writer reachability. |
| LPf_K027 | **OPEN.** Original array1736 constructor/reallocation1736-to 3472 is distinct from writer cap1768. Prior oracle obligations retain their original scope. |
| LPi_K017 | **OPEN.** Original array1736 constructor/reallocation1736-to 3472 is distinct from writer cap1768. Prior oracle obligations retain their original scope. |
| LPi_K018 | **OPEN.** Original array1736 constructor/reallocation1736-to 3472 is distinct from writer cap1768. Prior oracle obligations retain their original scope. |
| LPe_K017 | **OPEN.** Original roots/query cut caps128/256 and lengths64+4*i differ from writer cap1768 and lengths320+4*i. |

Per-row positive/control receipt links: [KND_ROW_CREDITS.json](KND_ROW_CREDITS.json). Previous authoritative KMZ credits are retained.

## Lean composition and native corroboration

`KND_Composition.schedule_composition` composes transitions over the schedule with every runtime equality as an explicit premise. Thirty-eight focused chunks prove membership/capacity/byte laws for all 116 entries; KND_partition proves their exact union. Nine row namespaces in eight modules retain original byte projections and add conditional writer composition. These models do not discharge missing heap facts or widen reachability.

Budget used: **Kani 90/90, Lean 50/50, optimized Rust 5/5**. The focused generic module precedes chunks and dependent row bridges; the final manifest is imported once. Each successful top theorem has an axioms audit limited to propext, Classical.choice and Quot.sound. [Exact run metrics](KND_RUNS.json). KND_L044 failed on recursion depth in an 80-entry membership decision and its sorryAx output is uncredited; KND_L045 replaces it with a symbolic filter-membership proof. No limit was raised. The two last row projections share a source to keep the 50-attempt budget. [Replacement record](KND_LEAN_REPLACEMENT.json).

Five optimized native runs check the 116-step schedule, 22 isolated query transitions, 64 checksum payloads, 64 selected weight lengths, and all finite original append-length domains. Every check includes a concrete XOR1 inequality. Native allocator witnesses do not replace symbolic Kani or function-oracle credit.

## Frozen scope and resource receipts

Frozen Rust revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Cargo.lock SHA256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. KMX patch SHA256: `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`. Exact stub SHA256: `c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9`.

Each Rust/Kani invocation validates the reused scratch crate resolved graph against its copied frozen lock, sets CARGO_NET_OFFLINE=true and opt-level3, and checks the lock hash afterwards. Every admitted scope requires reservation allowed:true AND exit 0, with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and one own scope at a time.

Maximum receipt RSS: 2944240 KiB; reported swaps 0 throughout. Exact targets, exits, wall times, RSS, swap, source revisions/hashes and axioms: [run index](KND_RUNS.json). [Admission audit](KND_ADMISSION_AUDIT.json), [transport](KMY_TRANSPORT.jsonl), [source archive](KND_SOURCE_ARCHIVE.json), [descriptive receipt-label errata](KND_RECEIPT_ERRATA.json).

No unchanged shape or final manifest was rerun. Persistent cache `/home/dombarker/project-offloads/codex-cx-kmy-cache-20261028` is retained. No crate/program file or wallet key/authority was changed, and no push occurred.

Final manifest [receipt](KND_L050/receipt.json): exit 0; wall 1.5439766350900754s; peak RSS 899988 KiB; swaps 0; source revision `42f27ec74a7a5c6a985552bb1829eb410d1fbc82`.
