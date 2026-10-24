# Port11PROV handoff

Branch `codex/cx-port11prov-20261024`, base
`7b887b23ac6e1fc5db1a30ff64fad11125935275`. New job-prefixed formal modules,
evidence and tools only. No shipped source, protocol, wire, feature, backend,
security contract, key, merge or push changes. Both deployed targets are NOT
established. The exact expression remains
`(Q+34)*B+kappa(Q+1161)+2^-126+2^-454`, `B=15/2^109`.

The concrete consumer is `Port11PROV_Authenticated.accepted`. See STAGE1.md
for the actual source chain and before/after statements, STAGE2.md for the
independent SOURCE1161 component audit, and GATES.md for precise retained
producers/ownership and the lead handoff. This remains an accepted-run local
source result; it does not establish classifier/no-hit or failure domination.

Validation and final budget are recorded in manifest.json. All attempted
sources and complete logs are retained, including elaboration failures.
No full frozen manifest, runtime suite, ELF rebuild or new artifact identity
gate was run. External compiled objects and accepted historical source
certificates are explicitly reused, not represented as a coherent release
rebuild. Resource caps remain 6G/8G/no-swap/Tasks64 and the global lock is used
on every launch. No resource cap or heartbeat/recursion override was raised.
