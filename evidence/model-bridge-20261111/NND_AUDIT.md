# Own-root verification

Target not yet established. This audits supporting proofs, not A1/A2 or ledger credit.

314 current own roots in149 modules; raw checked private declaration graph traversal passes, with exactly the standard axioms propext/Classical.choice/Quot.sound and zero cached-summary disagreements. Roots, current source receipts and archive pins are NND_AUDIT_ROOTS.json, NND_CURRENT_MODULES.json and NND_RAW_ARCHIVES.json. Eight control roots are separate: four planted hidden-axiom detections and four corresponding removal mutations. No old-ledger roots were audited.

The driver uses the exact ledger24-pinned NFA_WALKER/NFA_MemoryLimit objects and generated C support (NND_AUDIT_SUPPORT_IMPORTS.json/NND_AUDIT_C_PINS.json). It runs as an optimized native executable under the ordinary6G/8G/swap0/tasks64 scope. Its wrapper requires complete ordered root coverage and raw standard-only sets, and would report any cached-summary disagreement separately. It never trusts a cached summary in place of the raw graph.

L267 is the focused combined import, not a full release replay. L019 retains the selected combined closure; L058 verifies all selected bytes and archived evidence remain available. NND_VALIDATION.json checks300 unique actual formal scopes, two extraction attempts, zero Kani, source/input/log/archive hashes, frozen-source equality, and no file over20MB. No failed source snapshot enters the selected current roots.
