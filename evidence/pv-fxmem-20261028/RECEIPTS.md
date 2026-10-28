# Numbered compiler receipts

| ID | Module | Exit | Wall | Peak RSS KiB | Swap | Source revision | Credit |
|---|---|---:|---:|---:|---:|---|---|
| 35500 | PV_FXM_DropCounterexample | 1 | 0:00.18 | 474920 | 0 | cf19921d80 | rejected |
| 35501 | PV_FXM_DropCounterexample | 0 | 0:00.19 | 482492 | 0 | e82e62c591 | accepted |
| 35502 | PV_FXM_DropWorld | 1 | 0:00.27 | 484136 | 0 | 786826d2a5 | rejected |
| 35503 | PV_FXM_DropWorld | 0 | 0:00.31 | 494316 | 0 | ea00d7b71a | accepted |
| 35504 | PV_FXM_DropSelected | 1 | 0:01.28 | 2632948 | 0 | 0fe0c0ff66 | rejected |
| 35505 | PV_FXM_DropSelected | 0 | 0:01.35 | 2652748 | 0 | 140d86265f | accepted |
| 35506 | PV_FXM_ZeroWorld | 1 | 0:00.41 | 689028 | 0 | 771636c683 | rejected |
| 35507 | PV_FXM_ZeroWorld | 1 | 0:00.39 | 688968 | 0 | 0d5cc508d2 | rejected |
| 35508 | PV_FXM_ZeroWorld | 0 | 0:00.41 | 699996 | 0 | 250eb19663 | accepted |
| 35509 | PV_FXM_ZeroSelected | 1 | 0:01.36 | 2643976 | 0 | 988125ae4e | rejected |
| 35510 | PV_FXM_ZeroSelected | 0 | 0:01.42 | 2658476 | 0 | 59e450a540 | accepted |
| 35511 | PV_FXM_ZeroTrace | 0 | 0:00.26 | 694992 | 0 | 6f65f03c4a | accepted |
| 35512 | PV_FXM_ZeroConsumed | 0 | 0:01.33 | 2635140 | 0 | 6f65f03c4a | accepted |
| 35513 | PV_FXM_ReserveWorld | 1 | 0:01.47 | 2638480 | 0 | 79f784d26e | rejected |
| 35514 | PV_FXM_ReserveWorld | 1 | 0:01.50 | 2638324 | 0 | ffaf40a33c | rejected |
| 35515 | PV_FXM_ReserveWorld | 0 | 0:01.58 | 2654156 | 0 | 607d3bcfdc | accepted |
| 35516 | PDict_ReserveErrorSource | 1 | 0:01.22 | 2633904 | 0 | 4c1bb5531a | rejected |
| 35517 | PDict_ReserveErrorSource | 0 | 0:01.35 | 2633212 | 0 | 397210f27a | accepted |
| 35518 | PV_FXM_ReserveFacts | 1 | 0:00.09 | 191092 | 0 | 74c14e9aac | rejected |
| 35519 | PV_FXM_ReserveFacts | 1 | 0:01.35 | 2624976 | 0 | 5a9319e7ae | rejected |
| 35520 | PV_FXM_ReserveFacts | 0 | 0:01.45 | 2635636 | 0 | 417ed99555 | accepted |
| 35521 | PV_FXM_ReserveLayout | 1 | 0:01.61 | 2623968 | 0 | 417ed99555 | rejected |
| 35522 | PV_FXM_ReserveLayout | 0 | 0:01.37 | 2635280 | 0 | 560363ec96 | accepted |
| 35523 | PV_FXM_ReserveSelected | 1 | 0:01.95 | 2641820 | 0 | fb80a1e54c | rejected |
| 35524 | PV_FXM_ReserveSelected | 0 | 0:01.61 | 2655860 | 0 | f1b8126b5f | accepted |
| 35525 | PV_FXM_ReservePrimitive | 0 | 0:01.28 | 2635468 | 0 | 2a30d52542 | accepted |
| 35526 | PV_FXM_ReserveCaller | 0 | 0:01.22 | 2638676 | 0 | 2a30d52542 | accepted |
| 35527 | PV_FXM_Physical | 0 | 0:01.15 | 2642640 | 0 | 2a30d52542 | accepted |
| 35528 | PV_FXM_ZeroDrop | 1 | 0:01.16 | 2637044 | 0 | 7450488712 | rejected |
| 35529 | PV_FXM_ZeroDrop | 0 | 0:01.15 | 2643524 | 0 | 18bc1f3778 | accepted |
| 35597 | PV_FXM_AuditInstall | 0 | 0:01.82 | 2652704 | 0 | 348af6c81e | accepted |
| 35598 | PV_FXM_AuditAxioms | 0 | 0:01.22 | 2633636 | 0 | 348af6c81e | accepted |
| 35599 | PV_FXM_Closure | 0 | 0:01.13 | 2653656 | 0 | b4ad41705e | accepted |

Full target command, source blob/hash, dependency fingerprint, environment and raw #print axioms are in each numbered JSON and output log (private logs under lean-ID/). The inherited error type module has no added theorem; its axiom query count is zero. Refusals consume no compile attempts. No unchanged submitted compiler was rerun for receipt recovery.

35516 and 35518 are charged own-environment failures, corrected with changed output/import environments under rule 11. COOLDOWN-DEVIATION.json records one early retry; no cap or admission was bypassed. Legacy attempts 35500/35501 retain their accepted standing TasksMax=128 record; the observed current shared launcher and every private/native scope use TasksMax=64.
