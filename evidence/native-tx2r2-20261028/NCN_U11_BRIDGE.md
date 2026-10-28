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

## Stage 2: width32 split and Result contracts

NCN_K016/K017 and K018/K019 close the actual raw32 windows on the prefix
class 80+32*i (i<7) and tail class 632+32*i (i<2), respectively. Arbitrary
source/returned byte, source frame, pointer and cursor are checked as above.
This exact nine-site cover replaces the timed-out arbitrary-cursor shape;
it does not assert arbitrary-cursor raw32 totality.

NCN_K020 inverted ensures FAIL and K021 modifies violation FAIL are the first
two Result<K,Error> fidelity controls. NCN_K022 proves the actual Reader::k
weak cursor contract on the full1768 allocation: bounded cursor advances16,
including Err. NCN_K023 real zero-byte call is Ok. NCN_K024 cannot codegen
stub_verified because QM31/Error lack Arbitrary; no native credit. The owned
scratch repair adds cfg(kani)-only Arbitrary derives to the three field records
and Error. No repository shipped file is modified, and no source-body or domain
is changed. The unimplied-under-stub and call-site cursor controls remain pending.
A weak cursor contract never supplies byte or canonical-output correspondence.
