# RawK stage 1: head comparison ingredients

Checked source semantic preparation: RawK_PrepareHead.reached (012), preceded
by RawK_Head/InitHead/PublicHead/VerifyHead/SemanticHead, proves that successful
preparation's first successful query begins with byte85, the actual38-byte
r1_wire.DOMAIN. No new hypothesis replaces preparation acceptance. This is a
local source theorem, not yet the containing-account result.

Checked model: RawK_ModelHead.decision_head (015) proves that the first query
begins with byte16, for any H and admitted parsed/query-selected input.
It does not assume model acceptance. sortedPositions is nonempty by length
transport through mergeSort; no large finite enumeration or tree reduction.
Both rejected prefixes, duplicates, all six later checkpoint queries and early
exits remain in the original model; none can change position0.

Only standard axioms occur in successful receipts. Development failures are
retained and excluded. No ledger premise removed at this intermediate stage.
The remaining task is the source head on the same containing account/cuts.
