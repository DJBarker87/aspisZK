# NEV arithmetic continuation

Work in progress. Actual branch codex/cx-slice-q-mul3-20261103; requested predecessor branch name was 20261029. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Scope: batch_prefix_products, accumulate_batched_with_node, four_dots_one, four_dots, in that order. Budgets: 70 Kani,120 Lean,20 extraction. No push. No shipped sources changed.

NEI_/NEG_ results are reused, never reproved. Existing NEI/NEG objects are copied into the own cache with source/destination hashes in NEV_CACHE_IMPORTS.json; NEI_exports_20261103 takes priority. SInt2 and pinned Aeneas objects stay the canonical imported cohort. Native packets remain P6/D188 trust reclassification, not removal. The deployed 100-bit per-attempt target remains not established. L154 is a statement parameter; runtime trust, privacy and two-transaction design are unchanged.

Stage 0: read governing documents, predecessor member/obligation inventory, validator rejection reasons and sibling committed history. No predecessor/session-A workspace modified. No key created or touched. Inherited ELFs, not rebuilt: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

Exact native prefix frontier: arbitrary length<=110,index<length, initialized arbitrary old words, actual Vec::push same-index append and old-word/disjoint-flat frame. NEI_K041/K042 timeout shapes are excluded; metadata-only K039/K040 is insufficient. New experiment replaces variable-trip setup by guarded fixed-offset writes. All capacities/indices/old words remain arbitrary. No multiplication is executed in Kani.
