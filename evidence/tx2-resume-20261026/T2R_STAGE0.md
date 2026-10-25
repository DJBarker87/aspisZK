# TX2 resume stage 0

Target: strengthen AspisR1.Cons_Top.deployed on its original shared witnesses.
Branch codex/cx-tx2-resume-20261026. Prefix T2R_; budget 80 Lean attempts,
including dependencies, 0 Kani. No package replay. Target not yet established.

Read binding AGENTS.md including Security and proof discipline, common/local
rules, S2 ownership/lead plan/diagnosis, C3-BIN 01:20 route-B addendum and
S2LeadInterface (the historical files are under docs/research/100bit-spend-path-20261013).
Read Cons_Top/Result/Base/Caller/Continuation/Finish/Pair and Par handoff/delta.

Reuse coherent host /home/dombarker/project-offloads/codex-cx-sound-int2-20261025,
unchanged S2W launchers and pinned Cons_/Par_ objects. Initial scope inventory:
init.scope plus another worker NP6_K021; no foreign process touched.
Each compile: one module, lake env lean -j1 -M7000 -DElab.async=false,
MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64, timeout 180s.
No cap changes, unchanged timeout/OOM reruns, shipped changes or key operations.

Stages: specialise parameters at the actual Cons theorem; derive reader
variant/alpha observations and strengthen its same-tuple finish continuation;
then associate the selected transcript with the source proof where justified.
All removed/retained/added laws and quantifier changes will be audited against
the Cons_Top recount. Commit each stage locally, no push.
