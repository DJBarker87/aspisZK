# NCN U11 continuation

U11 OPEN; deployed target not yet established. Inherit NCI_U11_BRIDGE.md and
all its scoped results; no NCI fact is reproved or broadened.

## Stage 1: full checkpoint raw windows

NCN_K001/K002, K003/K004, K005/K006 establish the actual frozen Reader::raw
for widths 1, 4 and 16, arbitrary 1768-byte source, arbitrary bounded cursor,
and arbitrary observed return/source-frame byte. Cursor, source pointer and
length are retained. Matched opposite-byte controls fail under the identical
KMX configuration. These are native source-helper windows, not resume closure.
The KMX patch remains exactly bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.

NCN_K007: width32 timed out at 90 seconds; zero credit. K008 was not launched.
Do not repeat it unchanged. Next decomposition: one observed byte/half at fixed
return offset, plus KMX region/frame composition; no cap or timeout increase.
Widths16 and below now remove the earlier 64-byte-only allocation restriction
for those actual raw operations. Width32, caller installation, scalar Result
association, iteration and ownership still remain open. Full raw width32 must
not be inferred from width16 by changing the frozen helper's call pattern.

No cryptographic assumption, native model carrier, security game or metric
changed. Frozen Rust 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 unchanged in repo.
Exact commands/pins/exit/wall/RSS/swap are in NCN_ATTEMPTS.jsonl and receipts;
Kani axioms: not applicable. No ELF build trigger occurred.
