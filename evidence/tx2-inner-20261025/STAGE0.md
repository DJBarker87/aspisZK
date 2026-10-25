# TX2 inner stage 0

Branch codex/cx-tx2-inner-20261025. Scope: new Tx2N_ modules only; no shipped source changes.

Read parent AGENTS.md including Security and proof discipline, both scratchpad rules, S2 ownership handoff, lead plan, diagnosis, route B ruling, S2LeadInterface, Tx2I/Tx2Q/SInt2 handoffs and predecessor statements. Historical design paths resolve under docs/research/100bit-spend-path-20261013.

Budget: 80 Lean attempts including dependencies, 30 Kani runs. Initial usage 0/80, 0/30. Reuse sound-int2 coherent workspace and unchanged launchers. Each compile: one module, -M7000, MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64. No package replay. Initial other host scopes: s126-query-pairs and op5t-dep-47; left untouched.

Reading: install concrete reader/query/flush bodies, derive successful execution cuts on the same arguments, retain named Session A primitive laws. Never count a free-dictionary countermodel or replacement state-law premise as closure. Writer obligation remains the exact saved Vec equation. No change to protocol, source, wire, security metric or inherited artifact pins.
