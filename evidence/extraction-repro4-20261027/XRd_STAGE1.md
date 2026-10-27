# Second pinned release artifact

XRd_001 passed: Charon on identical 7978-file source snapshot at revision
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, identical features/preset/MIR and
rebuilt binaries daad69be… / efdbe5b8…. Only semantic command changes are the
kit opacity selectors, recorded in XRd_selector_delta.json. Output/cache paths
are job-local; no source/tool/library patch. Full command and environment are
XRd_release_candidate_charon_command.json.

New pinned LLBC: 80465ea37dd7c3c5becdd9c413d745ae076adf5b193067e8618d58db075c43e5,
12,864,440 bytes, has_errors=false, 605 function slots / 118 type slots.
Retain it on host as a second pinned artifact; do not overwrite 0814e4ec….
Exit0, wall95.709368s, peakRSS548468KiB, swap0. Full scope/resource/source
receipt: XRd_001/receipt.json. No Lean theorem/axiom result applies.

Read-only LLBC inventory confirms structured bodies for tx1, query_loop,
for_range, checkpoint, prepared_claim and canonical Dot methods; IDs changed
where new reachable bodies expanded the graph. Four known failing leaves are
Opaque (26,27,40,42). Aeneas coverage remains pending; source-body presence
is not a proof of projection or release association. No premise removed.
