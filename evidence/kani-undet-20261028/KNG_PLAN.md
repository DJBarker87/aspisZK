# Reconstruction plan

Frozen source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Frozen Cargo.lock SHA256: 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef.

23 NCS audit rows share 26 historical positive harness attempts. Inventory retains each historical receipt hash, harness name and all source pins. Reconstruct recorded properties from retained source recipes, not historical file identity. Preserve domains, assertion order and named cuts; record any unavailable detail as UNRECOVERABLE. Retain historical function names; new reconstruction modules use KNG_. No verdict-driven renaming.

Stages: (1) inventory and operating constraints; (2) reviewed reconstruction inputs and deployed-feature preflight; (3) serial positive/control runs and final per-row finding. Commit each completed stage. No push. Maximum 60 Kani / 10 Lean attempts across the whole job, including compilation failures. No Lean work is planned.

Every launch requires reservation allowed:true AND exit 0, one scope with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Reuse /home/dombarker/project-offloads/codex-cx-kmy-cache-20261028, never remove it. Existing runner only. Offline, optimized compilation. Validate graph against frozen lock before every run and lock unchanged after. Attach cargo metadata's resolved features for every crate to every run receipt. Exact KMX stubs where copies are reached; no substitute copy implementations; all named lower-law qualifications persist. Rule14 Option<fn>/function-pointer dependence is quarantined and gets no restoration credit.
