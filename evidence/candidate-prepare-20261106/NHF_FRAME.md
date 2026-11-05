# Adjacent-stage frames

| Transition | Established association | Remaining boundary |
|---|---|---|
| Heap → split | NGC complete heap packet; K007/K008 same owned14759 reply/error and split13831/928; NHF_HeapPrefix derives size from observed success and preserves reservation rejection | Parent emitted control composition |
| Split → semantic | Original proof[16..7031],7015 and actual left13831; arbitrary initial allocation; NGV_SemanticPacket.result constructs output;27 row logging/control pairs plus prefix32 | Parent emitted control composition; logging is not physical write replay |
| Semantic → values | Original proof[7031..7495],464 and right928; NGV_ExpandAssociation.result; opposite-window frames; overwrite and exact Vec back-functions | Parent emitted control composition |
| Values → view | NHF_Prefix derives actual split, SAME callee outputs, exact joined Vec and installed sourceView; no independent child outputs or successful parsing premise | Parent full body packet; view leaf separately CLOSED on caller domain |
| View → semantic verifier | Complete view Result including Parse; borrowed windows and error port fixed | TX1:137 full native/model verifier packet missing |
| Semantic verifier → Prepared::new | NFW control/error/scratch/Box partials retained read-only | TX1:179 full sampler/query/constructor packet missing |
| Prepared → returned Box/Vec | NFW control partials only | Same produced constructor record plus complete result/effects composition |

Prepare's own retained preconditions are the actual valid source carriers, exact stored length57607, current operation/statement parameters, root physical byte interpretation, tool/compiler/library/allocator/cleanup/ABI/source-to-ELF realization, and existing accepted runtime/cryptographic assumptions. Successful child calls, canonical raw inactive input, desired outputs, missing callee laws and independent post-state values are NOT new preconditions.

No claim is made about allocator capacity, Drop or physical runtime effects beyond the retained standard-library realization. The error and ordered-event frames are explicit. Arbitrary canonical/noncanonical original proof bytes are supported for the view leaf. Model frame results are not promoted into native whole-prepare credit.
