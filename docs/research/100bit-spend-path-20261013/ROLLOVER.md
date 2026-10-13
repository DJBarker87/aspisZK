# G_R1 rollover — design decision required

This deliverable takes the written-design-note option. The retained 255-pair transfer on the same v3b ELF fails even at the 1.4M ceiling, and ordinary v3b spends already exceed the lead's 1.3M bound. A 255-pair transfer/withdrawal fit is not established. No history format or spend-count policy is changed by this job.

## What the receipts establish

The ordinary v3b TxV0 transfer consumes 1,339,197 CU in tx1 and 1,344,689 CU in tx2; withdrawal consumes 1,337,836 / 1,360,982. All are the same across five capped runs. Those measurements include the Pool/adapter path. The per-phase breakdown is in [RECONCILIATION-P2.md](RECONCILIATION-P2.md).

The retained [255-pair v3b receipt](../../../results/gr1-cost-20261013/rollover/pool-transfer-pairs255-v0-v3b-run.json) and [log](../../../results/gr1-cost-20261013/rollover/pool-transfer-pairs255-v0-v3b-run.log) show the verifier receiving 1,286,943 CU in tx2, versus 1,352,738 CU on the ordinary 13-pair transfer. Thus **65,795 more CU is already spent before the verifier CPI starts** on this rollover fixture. This difference combines populated-history validation, changed lane/candidate work and rollover preparation; the retained Pool ELF has no internal markers to split them precisely.

The failing verifier reaches the `final` marker with 2,696 CU remaining, then exhausts its meter during the remaining return path: 1,286,887 of 1,286,943 CU consumed. The enclosing Pool reports 1,399,494 of 1,399,550. The transaction exhausts the 1.4M budget after its envelope overhead. This is a **lower bound**, not a completed rollover cost; no completion total or withdrawal rollover cost is invented. Its resource receipt has exit 1 because the harness expected success, with 4G/6G/swap-0 caps. The failure is retained rather than rerun unchanged.

A full history page contains 256 roots (8,256 bytes including its 64-byte header). Moving from 13 to 255 populated lane pairs changes both retained-history occupancy and the append boundary. Page validation/initialization and rollover-account work occur around settlement, in addition to the verifier work. The append also crosses a longer binary carry boundary at 255. These are distinct cost drivers; making the new page cheaper alone does not establish that the entire spend fits. A diagnostic at a higher compute budget could measure the remaining suffix, but would not satisfy the bound and is not presented as acceptance evidence.

## Options for the lead

| Option | Work moved or reduced | Cost/spend-count consequences and remaining decisions |
| --- | --- | --- |
| Separate maintenance transaction outside the spend count | Pre-create/initialize the next page and perform independently reusable preparation before the spend reaches the boundary. | Explicitly changes the transaction-count policy. Pays a separate transaction's envelope/account work and retains any spend-time checks that cannot be reused. The observed 65,795-CU prefix difference is not all automatically movable. Specify payer/rent, preparation lifetime, stale preparation handling and which exact work remains before measuring again. |
| Smaller history page | Reduce the number of roots/bytes scanned or initialized per page; rollover occurs more often. | Changes history layout, indexing, retention and account count. Costs must include more frequent page transitions and the longest lane-append boundary, not just an ordinary smaller page. Requires a chosen capacity and compatibility/migration decision before implementation. |
| Two-stage rollover | Split preparation/page work from final settlement across the two existing spend transactions, carrying a bounded prepared result/account into the final stage. | Could preserve the two-spend-transaction count, but shifts work into tx1, which is already roughly 38–39k CU above 1.3M in v3b. It therefore needs further verifier savings or a different query split as well. Specify prepared-state lifecycle, current-state revalidation and cleanup/account costs, then measure both stages. No caching/provenance assumption is accepted here. |

No option is selected. The lead must decide the cost/count/layout policy and any associated state-machine requirements. An implementation would then need five capped transfer and withdrawal runs at the boundary, mutation/rollback coverage, and the same receipt/dense-equivalence discipline. The current evidence supports leaving the rollover fit obligation open; it does not change the deployment verdict.
