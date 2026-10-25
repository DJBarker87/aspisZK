# GExq stage 0

Branch codex/cx-global-exp2-20261026, base 6c3a33f7e3. Read AGENTS.md,
r1p-common/local-lean, S2 ownership/plan/diagnosis/interface (historical paths
resolve under docs/research/100bit-spend-path-20261013), route B adoption,
GExp handoff/source interfaces and coherent SInt2 handoff.

Assigned endpoint rows L157, L159 and full L088 remain open initially. No
cryptographic contract, runtime premise or source pin changes are authorized.
New modules use GExq_; only those modules and this evidence directory will
change. Budget 100 Lean attempts including dependencies/prelaunches, 20 Kani.
Host preflight: ssh available; only init.scope populated. Existing SInt2
workspace/launchers/cache reused. Each invocation will use -j1 -M7000,
-DElab.async=false inside MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64.
No full replay, shipped source, keys or ELF changes planned.

First proof: split leaf-loop and terminal P6 cost. Existing body charges 288
every iteration; source branches prove continuing iterations contain only one
leaf read, whereas P6 verification occurs only in a terminating branch.
