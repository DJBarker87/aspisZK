# Checked native zero/P6 coupling and split CPI prefix obligations

No whole-P1 or global S2 row removed. Native enclosing metadata/decoder/PDA/copy association still missing. These are source-helper checks, not an actual runtime/history instance.

## Obligations discharged in their exact source class

K003–K008 split the predecessor timed-out PoolW_KANI039 into all six actual CPI error positions: create; top-up transfer/allocation/assignment; funded allocation/assignment. Each passes, checking actual instruction construction, three account infos, four signer seeds, call count, error propagation and no later call, plus the recording runtime's declared effect prefix from arbitrary initial effect state. Fixed native Rent::default; three funding representatives (zero,one,minimum), unchanged runtime trait and helper. Actual System effects and arbitrary runtime effects are not inferred.

K009 checks actual F400–415 shared zero guard against the SAME Boolean index scan extracted/proved by PoolW, on arbitrary192 bytes/funds/signer/rentEpoch in accepted owner/nonexecutable/writable metadata, default Rent, normal SDK cells. Return identity, successful guard release and arbitrary selected-byte/funds frame pass. K010 similarly couples actual P273–297 Pool-owned fresh mode to that scan. Other metadata/size/System-empty classes reuse predecessor native gates, not a new whole-source P1 theorem.

K011/K012 remove the predecessor's tiny-array restriction for copy-tail borrow errors: arbitrary384/192-byte data and supplied images, arbitrary funds and arbitrary selected bytes; master or checkpoint shared borrow prevents the relevant mutable borrow, propagates AccountBorrowFailed, releases acquired guards and leaves selected bytes/funds unchanged. K013 supplies the full192-byte guard borrow-error analogue. Normal distinct SDK allocations and fixed role keys/owner are explicit.

K015 passes FULL unrestricted native planner accepted selected-lane monotonicity. Arbitrary master, eight complete lane states (including roots/frontiers), root and bump; arbitrary selected lane. No coherent-input restriction or stub. This discharges the selected no-decrease statement only, not yet progress/all output fields or enclosing accepted-path coverage. K001 combined chronology and K002 scalar outputs timed out and are excluded; no unchanged rerun or cap increase.

## Extraction and Lean

P6 pure chronology reference isolated after source validate/order/capacity guards. CHARON001/AENEAS001 omitted scan and produced an unfilled template: excluded, never imported. CHARON002/AENEAS002 included scan but fixed arrays caused internal InterpBorrows2731 failure. Changed to slices and copied scalar loads before comparisons; CHARON003/AENEAS003 pass and complete Funs has no external template import.

PoolV_ChronologySource/Step/Suffix/Exact prove extracted scan total and exactly the pair of decreased/progressed existential comparisons over zipped arbitrary u64 slices. L001–004 pass; every theorem has printed standard axioms. P6/native chronology coupling and complete caller source correspondence remain open. No reference result is promoted to native whole-P1 evidence.

Every attempt receipt records exact target/command,source revision/hash,dependency fingerprint,exit,wall,RSS,swap and #print axioms (N/A for Kani/extraction). All scopes6G high/8G max/swap0/tasks64; Lean-M7000, optimized Rust. No shipped source changes, no ELF rebuild or package replay; historical three ELF pins remain inherited.
