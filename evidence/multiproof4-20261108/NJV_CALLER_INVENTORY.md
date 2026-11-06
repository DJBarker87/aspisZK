# NJV actual caller inventory

Target not yet established. Authoritative baseline: ledger15 NJO_LEDGER, 463/0/136 of599. NJV_BASELINE_ROWS.json retains both original obligations, every helper clause moved to the parent by NJO, frozen body hashes and obligation hashes without deletion or rewriting. NJV_CALLER_CLAUSES.json is their read-only extraction. The canonical incoming graph has exactly TX1:083 and TX2:055 candidate::batch_tree. The shared frozen source call is candidate.rs:202; each occurrence's actual batch/proof/queries/Prepared/root remains distinct. No caller is promoted here.

| Clause at SAME call | TX1:083 -> TX1:127 | TX2:055 -> TX2:093 |
|---|---|---|
| Arity Two | literal Arity::Two at native call; same 18-level model | literal Arity::Two, same 18-level model |
| Active count | caller's SAME d after sort/dedup must be positive and <=10 | preserve <=12 from queries10..21; <=10 is NOT derived from <=12. Generic entry law covers <=16 and rejection. Any consumer demanding the narrower ten-leaf unit must separately prove it; no such premise is silently imposed on TX2. |
| Sorted distinct idx<2^18 | SAME idx[..d], established by key ordering/dedup and entered successful node_count; caller must attach its own producer proof | SAME actual batch1 idx[..d], same obligation, not borrowed from TX1 |
| Node-count word slice | literal &nodes[..32*count], count from SAME node_count call; NJV_CallerBounds.from_count gives <=9216 | SAME current proof's batch1/tree0..2 slot and count, identical bound proof at its own keys |
| Zero padding / capacity | count<=SLOT_NODES[s] and chunks_exact(8) scan are source checks before this call; their complete library/source packet remains the caller's obligation | same current bytes, no first-proof persistence or NoBad premise |
| Full input identity / buffers | original idx/val mutable places, root and selected node prefix at this call; no alias beyond Rust's borrowing; no resets of inactive cells | same actual Prepared/proof and roots, preserve every index and digest cell and all earlier duplicate/error prefixes |
| Proof/query context | retain original proof length57607, batch0, its actual query subset and roots as named in baseline | retain proof length57607, batch1/tree0..2, queries10..21 distinct<2^18, SAME Prepared/proof, all ordered leaf/node digests and duplicate/error prefixes |

The generic convenience multiproof::verify caller is not an inventoried deployed incoming edge; no row or extra domain is inferred for it. The original unit clauses stay explicit on each actual caller even though the refinement root covers malformed counts/order and all 16 typed slots. Kernel-ready Domain records preserve the ten-leaf unit and exact padded-prefix identity separately. The only numeric root premise, <=9216 input bytes, is weaker than both actual counted domains. Parent caller proofs and next ledger credit remain external to this job.
