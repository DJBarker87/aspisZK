# Factory iteration continuation — unmerged, unadopted

Branch codex/cx-prover-rw-20261023, base745f551f8485241f7b5e74bf5945169dbf14b1fb.
Design1280b8fe81 precedes harness55cbf35245 and execution. No crates/programs,
protocol, wire, feature, security contract, installed tool/service, shared source,
wallet/key/RPC/chain, trust, merge, push or adoption changes. No full manifest.
Both deployed targets remain **not yet established**. Current ELF target pins
f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548
are unchanged targets, not new identity gates.

## Established component

Kani056 passes the concrete one-draw CANDIDATE cut relation, not the actual
factory loop. Full statement and limits: tools/prover-rw-20261023/factory-iteration/
RELATION.md and proof-cut/lib.rs. Every entry count0..15, nonce32, postbuffer64,
primitive Ok/Err choice, custom-u16 error code and ghost u64 provider token is
quantified. The stub requires exactly one freshzero64 call, permits arbitrary
postcontents on Err, and may advance the token on Err. The unchanged actual
From wraps the identical error. Some returns iff both halves are nonzero,
with exact moved32 owners and unchanged nonce; None iff either half is zero,
with retry=r+1 and remaining16-r decreasing by1. Entry15 rejection reaches16.
Success keeps retry unchanged. The arbitrary output index covers all32 bytes.
No desired-result premise, success/nonzero assumption, destructor replacement,
freshness, independence, uniformity or real OS hidden-state refinement.

The cut retains actual zeroize1.8.1 Drop and lexical owner scopes. This is a
sequential source/Kani component check, not native cleanup-event count/order,
physical post-destruction storage, unwind/abort, provenance/loan, stale-copy or
hardware-erasure evidence. The real whole-caller event producer remains open.

## Actual-source relation and retained failures

source.py --check validates original full source/span pins and exact erasure of
055's proof-only annotation.057 has a second explicit frame annotation, both
erase byte-for-byte to the same selected source. No executable source span in
those snapshots is rewritten.055 tests the actual loop invariant and complete
normal Result relation, with actual Drop and every safety/unwind check enabled.
It times out at240s. inspect001 records dynamic-contract write-set inclusion
and original-named loops; this does not identify an exact solver bottleneck.

The fallback candidate is a distinct statement:
actual `generate_for_mask_nonce : nonce32 -> Result<Secrets, Error>`;
cut `one_draw : (nonce32, r) -> Result<(r', Option<Secrets>), Error>`.
cut-source.py --check records exact body factoring, with only success-result
wrapping inside the copied body. Removed nonce guard/loop, entry retry and None
rejection plumbing are explicit. A cut rejection is not factory exhaustion.
Syntactic factoring is not a mechanized source/MIR equivalence proof. The
finite16 ranking argument is documented, conditional on this missing actual
body/caller association; it is NOT an accepted factory composition theorem.
No generic loop theorem replaces it. Existing theorem statements/premises are
unchanged; none was discharged, added or hidden.055 is no proof/counterexample.
