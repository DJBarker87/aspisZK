# PCG findings

## PCG-F1: ghost-context subobject provenance

Miri L055 rejects the initial local repr(C) oracle context recovery: a pointer derived from a shared32-byte program field is cast back to its containing context and retagged across sibling fields. The shared tag covers only bytes0..32. Miri reports invalid SharedReadOnly retag at offset32. The counter is local Cell, so this is not K-3; it is an unsafe-harness provenance defect. No shipped-source bug is claimed.

SUSPENDED pending repair: SDK K019/002,020/021,022/023,003/004,024/025,026/027,028/029,053/054; address379 K033/031 and seven address pairs034..047; master318 K059/060; digest368 K061/062. Context-bearing packets must NOT be consumed as CLOSED. The logical SDK/NFX/raw audits remain valid but do not repair native evidence. Pool CLOSED count remains zero.

Next: expose the original complete context provenance before taking the field borrow, restore that exposed provenance in the oracle, validate the repaired pattern with Miri, then rerun the affected ORIGINAL harness names with matched controls. No field-pointer reinterpretation will be silently retained as valid.

## PCG-F1 replacement evidence
The original receipts remain excluded. The repaired oracle exposes the entire original local Context allocation before making its shared subfield borrow, then restores that exposed provenance with `with_exposed_provenance`. Miri L057 exits0 on the repaired diagnostic (same pinned binary as L055). Original harness names are retained. SDK suite K092 exits0 for all eight; K083 fails all eight matched controls. Address suite K084/K085, master K086/K087 and digest K088/K089 pass/fail as intended. No function pointers or mutable statics introduced. Own task filter failures K082/K090/K091 reached no harness and confer no credit.
