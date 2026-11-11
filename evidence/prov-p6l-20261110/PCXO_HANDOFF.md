# PCXO_ (P6l) handoff

Script job on the Mac: 0 Lean, 0 extraction, 0 host scopes (one read-only ssh to read 22 module entries of l187_plan.json, cached in PCXO_PLAN_ENTRIES.json).

Run order from the worktree root:
1. `python3 -I evidence/prov-p6l-20261110/PCXO_citations.py --fetch` (once; later runs without --fetch use the cache)
2. `python3 -I evidence/prov-p6l-20261110/PCXO_recount.py` (about 30 s; reads research pinned at start; asserts the PCXN_ numbers before applying anything)

Outputs: PCXO_REPORT.md (counts first), PCXO_COUNTS.json, PCXO_HMO.json, PCXO_PARSE_BLOCKS_AUDIT.json, PCXO_CITATIONS.json, PCXO_TOOLS.json.

Open points for the lead: (1) the 6 keys whose only by-name externals are own-crate items (listed HMO_UNDETERMINED, subkind OWN_CRATE_NAME_BINDING_ONLY); (2) the 94 receipt-credited keys have no per-key external list and stay HMO_UNDETERMINED; (3) PCWR_, PCWS_, PCWT_ generators still carry the unfixed parse_blocks; (4) research moved during the run (the head is printed and stored in PCXO_COUNTS.json research_ref).

Target not yet established.
