# NBR TX1 prepare continuation

Stage 1: inspected the NBL/NBA handoff, frozen native prepare and canonical scan, closed leaf domains, and binding rules. Budget interpreted as min of instructions: 100 Lean attempts, 30 Kani runs. No inherited attempts counted as new runs.

Frozen revision: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Headline RPx_Deployed.deployed; no premise removal. Four NBL native dependencies remain open at start. Suspended wide_view/prepared_claim/expand_values/decode_k are conditional on K-1. No unmerged lane result credited.

Own runners copied from NBL with prefix/workspace/cache changes and stricter Kani budget only. Lead host infrastructure unchanged. Persistent cache is seeded by copying the retained leaf cache; hashes recorded before/after. Only NBR modules and this evidence directory may be edited. No shipped-source change or ELF rebuild trigger.
