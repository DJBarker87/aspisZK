# NMC failing steps

K001 map_public_cut: CBMC timeout at 90s, outer exit1, wall93.773818s, peak1864400KiB, swap0. No native credit or failing-control credit. The retired source snapshot is retained in the setup/receipt and patch history. Replacement: borrowed in-place Parent instead of synthetic full-record moves; cleanup explicitly remains a later segment. Same harness name; changed code and obligation frontier, not a rename or raised cap/timeout.

K002 borrowed full selector: CBMC timeout90s, exit1, wall92.468544s, peak1898804KiB, swap0. Retired. Isolate the scalar Result/update first, then ownership, Claims and remaining projected windows. No claim that one selected projection is the full segment. The original map_public_cut name is retained for the narrowed scalar shape, and the old full-frame obligation stays OPEN.

K021 terminal_guard_cut with full dynamic frame selector timed out90s; exit1, wall92.896063s, peak1811856KiB, swap0. Retired with no credit. Next shapes isolate exact Result plus owner, cell or byte projections per actual cut. All excluded frame projections remain named obligations; no weakened segment is promoted.

Heap carrier review: the initial Nat -> Option Claims type did not quantify arbitrary rest regions or their metadata/initializedness. It earned no physical row credit. It is replaced by Region.raw(base,extent,alignment,byte-initializedness) | Region.claims(full returned value). All affected own modules are rebuilt against the changed dependency; predecessor/source support is retained without promotion. Native full-heap realization remains OPEN.

K039 full terminal-entry positive and K040 matched inverse both timed out90s. K039 exit1/wall92.692609s/RSS3570464KiB; K040 exit1/wall92.432222s/RSS3450132KiB; both swap0. No entry/receiver/argument/return credit, and no matched-control credit. Replacement requires separate receiver identity, child arguments, full Result and each arbitrary-offset payload/frame window plus Lean composition. Budget40/40 is exhausted; these shapes are never rerun unchanged or with increased limits. K038 decode26 positive has no paired control and receives no native credit.
