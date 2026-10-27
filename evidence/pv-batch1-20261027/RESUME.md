# Resume under LOG D282 / ruling (l)

User-authorized resume from a964ac5c61. Source repair ccf87ccecd restores
weights.rs exactly to c57a344726; its op254 indexed body now lives in
cfg(prover) prover_powers.rs. Only prover.rs and sim.rs direct calls redirect.
See MODULE-GATES.md and revised-applied.diff. No other shipped-code changes.

Admission for stage transfer passed at 12:28:32 UTC. The immediate default
build reservation refused at 12:28:39 (reserved 59,995,324,416 bytes plus 8 GiB
above the 55 GiB safe limit); no scope started. Retry after 12:31:39 UTC.
No Lean attempt or env-J ID consumed. Shared env-J sources remain untouched.

The existing extraction draft now selects prover_powers.rs for op254.
Extraction and proof work are dependent on all three ELF pins passing.
Target not yet established; all callback/endpoint obligations remain open.

The first retry was sent at12:31:35 UTC, four seconds before the required
12:31:39 deadline. It also refused before a scope started. This was a wait
policy deviation; next retry is no earlier than12:34:35 UTC (three minutes
after the fresh refusal). No compile ran and no cap was bypassed.

Gate (a) default passed on retry4 at source ccf87ccecd: exact f8c0ec72…,
1,563,728bytes; exit0,41.435s,peak686356KiB,swap0. Devnet passed:
exact63ad3e9c…,1,563,728bytes; exit0,50.679s,peak685640KiB,swap0.
Pool is the remaining gate. No extraction or Lean scope started yet.
Retry3 refused at12:38:07 UTC with51,405,389,824bytes reserved; retry4
admitted after the next full wait with34,225,520,640bytes reserved.

Pool passed: exact121f3e29…,605704bytes; exit0,39.930s,peak678204KiB,swap0.
All three gate(a) pins passed; gate-a-resume.json contains the complete receipts.
