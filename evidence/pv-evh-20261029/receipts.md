# AGENTS.md section 6 focused receipts

| ID | Exact target | Exit | Wall | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---|---:|---:|---|
| 70400 | `PV_EVH_Interface` | 0 | 0:04.60 | 4129556 | 0 | `d174f79e1d890dcebff12d11b3a0951b6ed24d36` |
| 70401 | `PV_EVH_Core` | 0 | 0:42.08 | 4279988 | 0 | `4a55681402b5441982c0bbe94daa2ae87579b910` |
| 70402 | `PV_EVH_Residual` | 0 | 0:06.30 | 4120112 | 0 | `74a0931834e795475fa1a238906656108a5b0f47` |
| 70403 | `PV_EVH_Average` | 0 | 0:20.03 | 4245748 | 0 | `ee4de2ab7afb67094a77b12dd15950d161ded69b` |
| 70404 | `PV_EVH_Deployed` | 1 | 0:27.22 | 4227984 | 0 | `f13a6e38d30d6d2a459427e5cbc698af26e6d179` |
| 70405 | `PV_EVH_Deployed` | 0 | 0:31.26 | 4269456 | 0 | `f29dda9f9ce62a8ae6e9f20ebda794f56d23b97f` |
| 70406 | `PV_EVH_Satisfiability` | 1 | 0:19.33 | 4221536 | 0 | `f29dda9f9ce62a8ae6e9f20ebda794f56d23b97f` |
| 70407 | `PV_EVH_Satisfiability` | 1 | 0:18.02 | 4220244 | 0 | `a841db70808f378ebca43a63d5b952103686231f` |
| 70408 | `PV_EVH_ModelData` | 0 | 0:03.76 | 4188448 | 0 | `5be7ddf25a100a1439caa5e8e06b59dd8e80178d` |
| 70409 | `PV_EVH_Satisfiability` | 1 | 0:20.17 | 4221976 | 0 | `3242f051e4d402baccde4264f1d5efbdb80e723a` |
| 70410 | `PV_EVH_Satisfiability` | 0 | 0:21.27 | 4250804 | 0 | `3cdd5a36a1b8251751ff88511859482bfb2f363b` |
| 70411 | `PV_EVH_ClosedModel` | 0 | 0:18.82 | 4242044 | 0 | `3cdd5a36a1b8251751ff88511859482bfb2f363b` |
| 70498 | `PV_EVH_Axioms` | 0 | 0:04.01 | 4178824 | 0 | `6a7393306b5ea3824c9dcb779f4deac46e5c0a22` |
| 70499 | `PV_EVH_Replay` | 0 | 0:03.59 | 4179480 | 0 | `d114cea1b6a44f21f51b6344fd4ec9f59f4ba44f` |

Every row links by ID to `receipt-ID.json`, `out-ID.log`, `time-ID.log`.
The JSON receipts contain complete original #print axioms lines, source SHA256,
dependency fingerprint, admission result and exact capped command.
Rejected elaborations and their sorryAx diagnostic outputs are uncredited;
only accepted results with standard axioms are consumed.

Failed-source guard SHA256: `834712a75ce60216319f0ca6c22587412cdb913feb9b9cf69a1b90c43f1d82d6`.

Actual Lean launches: 14. Native scopes: 0. Kani: 0. VOID launches: 0.
Refused pre-compiler admission checks are retained separately and uncharged.
