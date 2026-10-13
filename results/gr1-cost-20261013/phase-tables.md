### Transfer tx1

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 56,875 | 45,843 | 58,172 | 54,662 | +11,032 |
| Semantic | 903,170 | 566,414 | 566,248 | 566,248 | +336,756 |
| Prepare | 489,141 | 155,355 | 155,379 | 155,379 | +333,786 |
| Checkpoint read | 0 | 0 | 0 | 0 | +0 |
| Merkle | 100,280 | 108,318 | 108,404 | 108,404 | -8,038 |
| Query folds and rho accumulation | 822,065 | 386,845 | 386,817 | 386,817 | +435,220 |
| Relation rounds and pairing | 0 | 0 | 0 | 0 | +0 |
| Final rho | 0 | 0 | 0 | 0 | +0 |
| Checkpoint write | 68,211 | 67,126 | 67,128 | 67,128 | +1,085 |
| Entry/exit | 1,309 | 1,309 | 53 | 53 | +0 |
| Verifier subtotal | 2,441,051 | 1,331,210 | 1,342,201 | 1,338,691 | +1,109,841 |
| Pool/custody outside verifier | 0 | 0 | 0 | 0 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,441,407 | 1,331,566 | 1,342,257 | 1,339,197 | +1,109,841 |

### Transfer tx2

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 36,136 | 30,385 | 63,757 | 33,782 | +5,751 |
| Semantic | 0 | 0 | 0 | 0 | +0 |
| Prepare | 0 | 0 | 0 | 0 | +0 |
| Checkpoint read | 114,865 | 107,357 | 107,367 | 107,367 | +7,508 |
| Merkle | 120,355 | 129,876 | 129,920 | 129,920 | -9,521 |
| Query folds and rho accumulation | 983,707 | 463,946 | 463,991 | 463,991 | +519,761 |
| Relation rounds and pairing | 1,059,165 | 526,890 | 526,890 | 526,890 | +532,275 |
| Final rho | 94,175 | 20,962 | 20,962 | 20,962 | +73,213 |
| Checkpoint write | 1,783 | 1,267 | 0 | 0 | +516 |
| Entry/exit | 1,306 | 1,306 | 7,780 | 7,780 | +0 |
| Verifier subtotal | 2,411,492 | 1,281,989 | 1,320,667 | 1,290,692 | +1,129,503 |
| Pool/custody outside verifier | 0 | 0 | 53,491 | 53,491 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,411,848 | 1,282,345 | 1,374,214 | 1,344,689 | +1,129,503 |

### Withdrawal tx1

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 56,823 | 45,791 | 58,063 | 54,553 | +11,032 |
| Semantic | 899,866 | 565,114 | 565,063 | 565,063 | +334,752 |
| Prepare | 489,020 | 155,356 | 155,341 | 155,341 | +333,664 |
| Checkpoint read | 0 | 0 | 0 | 0 | +0 |
| Merkle | 100,222 | 108,462 | 108,360 | 108,360 | -8,240 |
| Query folds and rho accumulation | 819,546 | 386,805 | 386,832 | 386,832 | +432,741 |
| Relation rounds and pairing | 0 | 0 | 0 | 0 | +0 |
| Final rho | 0 | 0 | 0 | 0 | +0 |
| Checkpoint write | 68,211 | 67,126 | 67,128 | 67,128 | +1,085 |
| Entry/exit | 1,309 | 1,309 | 53 | 53 | +0 |
| Verifier subtotal | 2,434,997 | 1,329,963 | 1,340,840 | 1,337,330 | +1,105,034 |
| Pool/custody outside verifier | 0 | 0 | 0 | 0 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,435,353 | 1,330,319 | 1,340,896 | 1,337,836 | +1,105,034 |

### Withdrawal tx2

| Phase (CU) | P2 S2 | d18 | Adapter v2 (TxV1) | Adapter v3b (TxV0) | P2 − d18 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Parse | 36,136 | 30,385 | 63,696 | 33,721 | +5,751 |
| Semantic | 0 | 0 | 0 | 0 | +0 |
| Prepare | 0 | 0 | 0 | 0 | +0 |
| Checkpoint read | 114,779 | 107,357 | 107,342 | 107,342 | +7,422 |
| Merkle | 120,480 | 129,882 | 129,948 | 129,948 | -9,402 |
| Query folds and rho accumulation | 986,011 | 463,860 | 464,010 | 464,010 | +522,151 |
| Relation rounds and pairing | 1,059,243 | 526,930 | 527,061 | 527,061 | +532,313 |
| Final rho | 94,148 | 20,962 | 20,962 | 20,962 | +73,186 |
| Checkpoint write | 1,783 | 1,267 | 0 | 0 | +516 |
| Entry/exit | 1,306 | 1,306 | 7,773 | 7,773 | +0 |
| Verifier subtotal | 2,413,886 | 1,281,949 | 1,320,792 | 1,290,817 | +1,131,937 |
| Pool/custody outside verifier | 0 | 0 | 69,659 | 69,659 | +0 |
| Transaction overhead | 356 | 356 | 56 | 506 | +0 |
| Whole transaction | 2,414,242 | 1,282,305 | 1,390,507 | 1,360,982 | +1,131,937 |

