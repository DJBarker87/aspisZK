# MERGE GATE v2: CLEAN

Ruling h′ / LOG D255. Research `01c21de60b7146226f258c778fb9e29eaf4d1409`. PROJECT objects 1028, gaps 0; EXTERNAL objects 5640, gaps 0.

The three previously reported gaps were comparisons against the wrong file paths under the former ruling (h). The rebuild resolution record selects accepted-current sources; their current research bytes and shared sources match the accepted rebuild source/object receipts. No shared source or object was overwritten or recompiled for this correction. There is no changed dependency object and therefore no changed-input dependent cone to rebuild. The final allocation-9 audit is the required full kernel replay with these exact objects. Prior gap reports remain historical evidence, superseded by D255.

Exact source/object links, every external manifest link, rebuild-cohort paths, and all effective object hashes are in resume9-merge-gate-v2.json and resume9-rebuild-resolved-paths.json. Where the rebuild lists multiple cohorts, the exact shared source SHA and the effective object receipt select the matching entry; a module name alone never selects a path. Branch additions are individually receipt-linked. Historical changed-input replay flags remain historical and are not reported as fresh replays.

Final audit: 42804 (third shard; all three receipts in resume9-attempts.jsonl).

Post-audit exact input/object hashes unchanged: 6662.

Read-only RunJoin dependency: 25 published sources pinned at 414d6fb38c, unchanged at 0a6a5428a8. They are owned by the live RunJoin branch and must be integrated alongside this consumer; no implementation source was duplicated here. Their accepted owner receipts, exact source hashes and consumer object hashes are retained in resume9-model-pins.json. This gate is source/object coherence for the named branch cohort, not deployed Records identification.

Remaining gaps: none.
