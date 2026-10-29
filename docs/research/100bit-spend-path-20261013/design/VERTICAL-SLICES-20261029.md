# Vertical slices (lead decision, 2026-10-29)

Owner, 2026-10-29: "i feeel like we should spend less time on individual groundwork and tryt and get a couple of big vertical slices done".

Diagnosis (NDT_ ledger, research 94f912c16b): all 587 composed rows are OPEN for the same reason. No per-edge caller-domain certificate has been instantiated anywhere. Even subtrees that are fully bridged function by function (verifier.rs::prepared_claim, 38 functions; encode/validate terminal statement, 29 and 25) have never been composed. Horizontal frontier lanes added local bridges but no composition. The five lanes NDU_-NDY_ were stopped at WIP snapshots on their branches; those snapshots are unreviewed material, not credit.

Change of method: work is organised as two vertical slices. In each slice one job closes the slice's OPEN functions (four-part bridges) and one job composes: it discharges every internal call-domain obligation bottom-up, and the named PacketDomain/PhysicalInterpretation hypotheses of inner calls, up to one composed theorem per slice root. That theorem's only hypotheses are the root's own domain and interpretation plus the listed trust rows. Definitions, with the exact function, edge and row lists, are in VERTICAL-SLICES-20261029.json (generated from NDT_LEDGER.json).

- Slice Q, the query check (TX1 and TX2 share it): roots candidate.rs::query_loop and verifier.rs::QueryGeometry::for_range. 78 functions, 20 OPEN, 257 internal edges, 149 inventory rows.
- Slice S, statement binding and result: TX1 decode_public_statement_box and validate terminal statement; TX2 encode terminal statement, reconstruct_asq8_statement, decode terminal request, scan_proof_buffer, emit_result. 61 functions, 19 OPEN, 129 edges, 97 rows.

Progress is reported as composed rows CLOSED under the NDT_ semantics. Local bridges count only as inputs to that. A slice is done when its roots' composed status is CLOSED, validated by an NDT_validate.py run on a ledger copy. Neither slice by itself removes the headline's extraction premise. Each slice is a complete, checkable sub-path of it, and the next slices (Prepared::new, finish_relation, batch_merkle, verify_finish) follow the same pattern.
