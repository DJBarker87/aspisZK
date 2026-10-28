# D350 merged candidate adoption gate

In progress. Candidate `82566acdfb488183022f41ac564c11df22c9404f`, branch `codex/pv-gate6-20261028`, exact worktree `/Users/dominic/ZK/.worktrees/pv-gate6`. Host directory `/home/dombarker/project-offloads/codex-pv-gate6-20261028/`.

Stage A: fresh default/devnet/Pool ELF rebuild and pin comparison; pinned 1.94.1 devnet_spend client; fixed coin0 against retained SHA-checked 37e5e133f8 control; fresh seeds6000–6999 whole-prover differential against c57a344726 using pv-integ4's harness, comparator, concurrency and scope recipe. D328 criterion compares proof, public, ledger and canonical result bytes, excluding elapsed seconds only.

Stage B is conditional on Stage A PASS. Ten alternating paired fresh processes per side, coins100–109 (minimum five unthrottled pairs), fixed CPU affinity, both transfer and withdrawal per process. Record package temperature and throttle counters before and after each pair, separate throttled pairs. Gate per fixture: candidate median strictly below15s, ratio of candidate/control medians at most1.10. Quiet marker must be written before drain, last at most1500s, never extended; drain at most600s. Trap removes own marker immediately when measurement ends or process exits. Partial receipts retained on expiry.

No implementation source change, Lean or Kani. All native workloads use serial capped host scopes: MemoryHigh6G, MemoryMax8G, MemorySwapMax0, TasksMax64; optimized Rust -j4. Admission requires allowed:true and exit0. Resource refusal waits180s, maximum10 retries. Source exports are checked against exact git blobs. No binaries, keys or raw proof bytes committed. Only task-owned Cargo targets will be removed.

This is finite artifact, functional and timing validation. Premises before/after unchanged: removed0, added0, weakened0, changed0. T remains entropy_law, entropy_kernel, observation. Source-to-model/deployed endpoint closure, E1/E2, real RunJoin, entropy/kernel bridge, OS-failure independence, inversion boundary, client proof-account adoption and L1/L2/L3 retain their substantive proof and deployment obligations. Target not yet established.

## Stage A interim results

All three freshly rebuilt ELF pins match. Default47.223s/684472KiB RSS, devnet33.067s/687096KiB, Pool55.832s/676608KiB, all exit0/swap0. Client build140.266s/640276KiB, rustc1.94.1(e408947bfd200af42db322daf0fadfe7e26d3bd1), LLVM21.1.8. Client SHA256 `0d9dbd91d4eb9b4add14e164f8ffa14196ca7978c506a021eef057c5cefaa544`,2882024bytes. Exact recommended features and rustc-vV are retained in build-client/.

Coin0 transfer/withdrawal PASS against retained SHA-verified37e5e133f8 control outputs: proof,public,ledger and canonical result bytes all identical. Raw records differ in seconds only. Fresh candidate generation30.434s/668612KiB RSS,exit0/swap0. Harness build57.447s/570808KiB. Initial proof-generation admission refused before execution; retry after180s succeeded. No unchanged proof run repeated.

Initial upload was refused on the55GiB aggregate reservation; first180s retry also refused; second succeeded. Every exported candidate input matches exact Git bytes(7496files). Shipped-control source identity is independently verified in control-source-identity.json. New differential cohort remains pending.
